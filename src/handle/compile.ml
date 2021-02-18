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

(** [compile force mp] compiles the file corresponding to [mp], when it is
    necessary (the corresponding object file does not exist,  must be updated,
    or [force] is [true]).  In that case,  the produced signature is stored in
    the corresponding object file. *)
let rec compile : bool -> Path.t -> Sign.t = fun force mp ->
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
        fatal_no_pos "Both \"%s\" and \"%s\" exist." src legacy
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
  if Path.Map.mem mp !loaded then
    let sign = Path.Map.find mp !loaded in
    Console.out 2 "%a already loaded\n" Print.pp_path mp; sign
  else if force || Extra.more_recent (src ()) obj then
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
      let handle ss c =
        Term.Meta.reset_meta_counter ();
        (* We provide the compilation function to the handle commands, so that
           "require" is able to compile files. *)
        let (ss, p, _) = Command.handle (compile false) ss c in
        match p with
        | None       -> ss
        | Some(data) ->
            let (st,tacs) = (data.pdata_p_state, data.pdata_tactics) in
            let e = data.pdata_expo in
            let st =
              List.fold_left
                (fun st tac -> fst (Tactic.handle ss e st tac))
                st tacs
            in
            data.pdata_finalize ss st
      in
      let consume cmd = Stdlib.(sig_st := handle !sig_st cmd) in
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
      Path.Map.iter (fun mp _ -> ignore (compile false mp)) !(sign.sign_deps);
      loaded := Path.Map.add mp sign !loaded;
      Sign.link sign;
      Console.out 2 "Loaded \"%s\"\n%!" obj; sign
    end

(** [recompile] indicates whether we should recompile files who have an object
    file that is already up to date. Note that this flag only applies to files
    that are given on the command line explicitly, not their dependencies. *)
let recompile = Stdlib.ref false

(** [compile_file fname] is the main compiling function. It is called from the
    main program exclusively. *)
let compile_file : string -> Sign.t = fun fname ->
  Package.apply_config fname;
  (* Compute the module path (checking the extension). *)
  let mp = path_of_file fname in
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
