(** High-level compilation functions. *)

open! Lplib
open Lplib.Extra

open Timed
open Sign
open Console
open Files

(** [gen_obj] indicates whether we should generate object files when compiling
    source files. The default behaviour is not te generate them. *)
let gen_obj = Stdlib.ref false

(** [parse_file fname] selects and runs the correct parser on file [fname], by
    looking at its extension. *)
let parse_file : string -> Syntax.ast = fun fname ->
  match Filename.check_suffix fname src_extension with
  | true  -> Parser.parse_file fname
  | false -> Parser.Legacy.parse_file fname

(** [compile force path] compiles the file corresponding to [path], when it is
    necessary (the corresponding object file does not exist,  must be updated,
    or [force] is [true]).  In that case,  the produced signature is stored in
    the corresponding object file. *)
let rec compile : bool -> Path.t -> Sign.t = fun force path ->
  (* Remove escaping quotes from module paths. *)
  let remove_quote p =
    if Lp_lexer.is_escaped p then
      String.(sub p 2 (length p - 4))
    else p
  in
  let base = Files.module_to_file (List.map remove_quote path) in
  let src () =
    (* Searching for source is delayed because we may not need it
       in case of "ghost" signatures (such as for unification rules). *)
    let src = base ^ src_extension in
    let legacy = base ^ legacy_src_extension in
    match (Sys.file_exists src, Sys.file_exists legacy) with
    | (false, false) -> fatal_no_pos "File [%s.{lp|dk}] not found." base
    | (true , true ) -> fatal_no_pos "Both [%s] and [%s] exist." src legacy
    | (true , false) -> src
    | (false, true ) -> legacy
  in
  let obj = base ^ obj_extension in
  if List.mem path !loading then
    begin
      fatal_msg "Circular dependencies detected in [%s].\n" (src ());
      fatal_msg "Dependency stack for module [%a]:\n" Path.pp path;
      List.iter (fatal_msg "  - [%a]\n" Path.pp) !loading;
      fatal_no_pos "Build aborted."
    end;
  if PathMap.mem path !loaded then
    let sign = PathMap.find path !loaded in
    out 2 "Already loaded [%a]\n%!" Path.pp path; sign
  else if force || Files.more_recent (src ()) obj then
    begin
      let forced = if force then " (forced)" else "" in
      let src = src () in
      out 2 "Loading [%s]%s\n%!" src forced;
      loading := path :: !loading;
      let sign = Sig_state.create_sign path in
      let sig_st = Sig_state.of_sign sign in
      (* [sign] is added to [loaded] before processing the commands so that it
         is possible to qualify the symbols of the current modules. *)
      loaded := PathMap.add path sign !loaded;
      let handle ss c =
        Terms.Meta.reset_key_counter ();
        (* We provide the compilation function to the handle commands, so that
           "require" is able to compile files. *)
        let (ss, p) = Handle.handle_cmd (compile false) ss c in
        match p with
        | None       -> ss
        | Some(data) ->
            let (st,ts) = (data.pdata_p_state, data.pdata_tactics) in
            let e = data.pdata_expo in
            let st = List.fold_left (Tactics.handle_tactic ss e) st ts in
            data.pdata_finalize ss st
      in
      ignore (List.fold_left handle sig_st (parse_file src));
      (* Removing private symbols from signature. *)
      let not_prv _ sym = not (Terms.is_private sym) in
      let not_prv_fst k s_ = not_prv k (fst s_) in
      sign.sign_symbols := StrMap.filter not_prv_fst !(sign.sign_symbols);
      sign.sign_builtins := StrMap.filter not_prv !(sign.sign_builtins);
      sign.sign_unops := StrMap.filter not_prv_fst !(sign.sign_unops);
      sign.sign_binops := StrMap.filter not_prv_fst !(sign.sign_binops);
      if Stdlib.(!gen_obj) then Sign.write sign obj;
      loading := List.tl !loading;
      out 1 "Checked [%s]\n%!" src; sign
    end
  else
    begin
      out 2 "Loading [%s]\n%!" (src ());
      let sign = Sign.read obj in
      PathMap.iter (fun mp _ -> ignore (compile false mp)) !(sign.sign_deps);
      loaded := PathMap.add path sign !loaded;
      Sign.import_ops sign;
      Sign.link sign;
      out 2 "Loaded  [%s]\n%!" obj; sign
    end

(** [recompile] indicates whether we should recompile files who have an object
    file that is already up to date. Note that this flag only applies to files
    that are given on the command line explicitly, not their dependencies. *)
let recompile = Stdlib.ref false

(** [compile_file fname] is the main compiling function. It is called from the
    main program exclusively. *)
let compile_file : file_path -> Sign.t = fun fname ->
  Package.apply_config fname;
  (* Compute the module path (checking the extension). *)
  let mp = Files.file_to_module fname in
  (* Run compilation. *)
  compile Stdlib.(!recompile) mp
(** Pure wrappers around compilation functions. Functions provided perform the
    same computations as the ones defined earlier, but restores the state when
    they have finished. An optional library mapping or state can be passed as
    argument to change the settings. *)
module Pure : sig
  val compile : ?lm:string -> ?st:State.t -> bool -> Path.t -> Sign.t
  val compile_file : ?lm:string -> ?st:State.t -> file_path -> Sign.t
end = struct

  (* [pure_apply_cfg ?lm ?st f] is function [f] but pure (without side
     effects).  The side effects taken into account occur in
     {!val:Console.State.t}, {!val:Files.lib_mappings} and in the meta
     variable counter {!module:Terms.Meta}. Arguments [?lm] allows to set the
     library mappings and [?st] sets the state. *)
  let pure_apply_cfg : ?lm:string -> ?st:State.t -> ('a -> 'b) -> 'a -> 'b =
    fun ?lm ?st f x ->
    let libmap = !lib_mappings in
    State.push ();
    Option.iter new_lib_mapping lm;
    Option.iter State.apply st;
    let restore () =
      State.pop ();
      lib_mappings := libmap
    in
    try
      let res = f x in
      restore (); res
    with e -> restore (); raise e

  let compile ?lm ?st force path =
    let f (force, path) = compile force path in
    pure_apply_cfg ?lm ?st f (force, path)

  let compile_file ?lm ?st = pure_apply_cfg ?lm ?st compile_file
end
