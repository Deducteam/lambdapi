(** High-level compilation functions. *)

open! Lplib

open Timed
open Common
open Error
open Parsing
open Core
open Sign
open Library

(** [gen_obj] indicates whether we should generate object files when compiling
    source files. The default behaviour is not te generate them. *)
let gen_obj = Stdlib.ref false

(** [parse_file fname] selects and runs the correct parser on file [fname], by
    looking at its extension. *)
let parse_file : string -> Syntax.ast = fun fname ->
  match Filename.check_suffix fname src_extension with
  | true  -> Parser.parse_file fname
  | false -> Parser.Dk.parse_file fname

(** [compile_with ~handle ~force mp] compiles the file corresponding to module
   path [mp] using function [~handle] to process commands. Module [mp] is
   processed when it is necessary, i.e. the corresponding object file does not
   exist, or it must be updated, or [~force] is [true]. In that case, the
   produced signature is stored in the corresponding object file if the option
   [--gen_obj] or [-c] is set. *)
let rec compile_with :
  handle:(Command.compiler -> Sig_state.t -> Syntax.p_command -> Sig_state.t)
  -> force:bool -> Command.compiler =
  fun ~handle ~force mp ->
  let base = file_of_path mp in
  let src () =
    (* Searching for source is delayed because we may not need it
       in case of "ghost" signatures (such as for unification rules). *)
    let src = base ^ src_extension in
    let legacy = base ^ legacy_src_extension in
    match (Sys.file_exists src, Sys.file_exists legacy) with
    | (false, false) ->
        fatal_no_pos "File \"%s.lp\" (or .dk) not found." base
    | (true , true ) ->
        wrn None "Both \"%s\" and \"%s\" exist. We take \"%s\"."
          src legacy src; src
    | (true , false) -> src
    | (false, true ) -> legacy
  in
  let obj = base ^ obj_extension in
  if List.mem mp !loading then
    begin
      fatal_msg "Circular dependencies detected in \"%s\".\n" (src ());
      fatal_msg "Dependency stack for module %a:\n" Print.pp_path mp;
      List.iter (fatal_msg "- %a\n" Print.pp_path) !loading;
      fatal_no_pos "Build aborted."
    end;
  match Path.Map.find_opt mp !loaded with
  | Some sign ->
    Console.out 2 "%a already loaded\n" Print.pp_path mp; sign
  | None ->
    if force || Extra.more_recent (src ()) obj then
    begin
      let forced = if force then " (forced)" else "" in
      let src = src () in
      Console.out 1 "Loading \"%s\"%s ...\n%!" src forced;
      loading := mp :: !loading;
      let sign = Sig_state.create_sign mp in
      let sig_st = Stdlib.ref (Sig_state.of_sign sign) in
      (* [sign] is added to [loaded] before processing the commands so that it
         is possible to qualify the symbols of the current modules. *)
      loaded := Path.Map.add mp sign !loaded;
      Stdlib.(Tactic.admitted := -1);
      let consume cmd =
        Stdlib.(sig_st :=
                  handle (compile_with ~handle ~force:false) !sig_st cmd)
      in
      Stream.iter consume (parse_file src);
      Sign.strip_private sign;
      if Stdlib.(!gen_obj) then Sign.write sign obj;
      loading := List.tl !loading;
      Console.out 1 "Checked \"%s\"\n%!" src; sign
    end
    else
    begin
      Console.out 2 "Loading \"%s\" ...\n%!" (src ());
      let sign = Sign.read obj in
      let compile mp _ = ignore (compile_with ~handle ~force:false mp) in
      Path.Map.iter compile !(sign.sign_deps);
      loaded := Path.Map.add mp sign !loaded;
      Sign.link sign;
      (* Since Unif_rule.sign is always assumed to be already loaded, we need
         to explicitly update the decision tree of Unif_rule.equiv since it is
         not done in linking which normally follows loading. *)
      let sm = Path.Map.find Unif_rule.path !(sign.sign_deps) in
      if Extra.StrMap.mem Unif_rule.equiv.sym_name sm then
        Tree.update_dtree Unif_rule.equiv;
      Console.out 2 "Loaded \"%s\"\n%!" obj; sign
    end

(** [compile force mp] compiles module path [mp] using
    {!val:Command.with_proofs}, forcing compilation of up-to-date files if
    [force] is true. *)
let compile force = compile_with ~handle:Command.handle ~force

(** [recompile] indicates whether we should recompile files who have an object
    file that is already up to date. Note that this flag only applies to files
    that are given on the command line explicitly, not their dependencies. *)
let recompile = Stdlib.ref false

(** [compile_file fname] is the main compiling function. It is called from the
    main program exclusively. *)
let compile_file : string -> Sign.t = fun fname ->
  Package.apply_config fname;
  (* Compute the module path (checking the extension). *)
  let mp = path_of_file LpLexer.escape fname in
  (* Run compilation. *)
  compile Stdlib.(!recompile) mp

open Console

(** Pure wrappers around compilation functions. Functions provided perform the
    same computations as the ones defined earlier, but restores the state when
    they have finished. An optional library mapping or state can be passed as
    argument to change the settings. *)
module Pure : sig
  val compile : ?lm:string*string -> ?st:State.t -> bool -> Path.t -> Sign.t
  val compile_file : ?lm:string*string -> ?st:State.t -> string -> Sign.t
end = struct

  (* [pure_apply_cfg ?lm ?st f] is function [f] but pure (without side
     effects). The side effects taken into account occur in {!val:State.t} and
     {!val:Library.lib_mappings}. Arguments [?lm] allows to set the library
     mappings and [?st] sets the state. *)
  let pure_apply_cfg :
        ?lm:string*string -> ?st:State.t -> ('a -> 'b) -> 'a -> 'b =
    fun ?lm ?st f x ->
    let libmap = !lib_mappings in
    State.push ();
    Option.iter Library.add_mapping lm;
    Option.iter State.apply st;
    let restore () =
      State.pop ();
      lib_mappings := libmap
    in
    try
      let res = f x in
      restore (); res
    with e -> restore (); raise e

  let compile ?lm ?st force mp =
    let f (force, mp) = compile force mp in
    pure_apply_cfg ?lm ?st f (force, mp)

  let compile_file ?lm ?st = pure_apply_cfg ?lm ?st compile_file
end
