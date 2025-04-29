(** High-level compilation functions. *)

open Lplib
open Timed
open Common open Error open Library
open Parsing
open Core open Sign

(** [gen_obj] indicates whether we should generate object files when compiling
    source files. The default behaviour is not te generate them. *)
let gen_obj = Stdlib.ref false

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
  if mp = Ghost.path then Ghost.sign else
  let base = file_of_path mp in
  let src =
    let lp_src = base ^ lp_src_extension in
    let dk_src = base ^ dk_src_extension in
    match (Sys.file_exists lp_src, Sys.file_exists dk_src) with
    | (false, false) ->
        fatal_no_pos "File \"%s.lp\" (or .dk) not found." base
    | (true , true ) ->
        wrn None "Both \"%s\" and \"%s\" exist. We take \"%s\"."
          lp_src dk_src lp_src; lp_src
    | (true , false) -> lp_src
    | (false, true ) -> dk_src
  in
  let obj = base ^ obj_extension in
  if List.mem mp !loading then
    begin
      fatal_msg "Circular dependencies detected in \"%s\".@." src;
      fatal_msg "Dependency stack for module %a:@." Path.pp mp;
      List.iter (fatal_msg "- %a@." Path.pp) !loading;
      fatal_no_pos "Build aborted."
    end;
  match Path.Map.find_opt mp !loaded with
  | Some sign -> sign
  | None ->
    if force || Extra.more_recent src obj then
    begin
      let forced = if force then " (forced)" else "" in
      Console.out 1 "Check \"%s\"%s ..." src forced;
      loading := mp :: !loading;
      let sign = Sig_state.create_sign mp in
      let sig_st = Stdlib.ref (Sig_state.of_sign sign) in
      (* [sign] is added to [loaded] before processing the commands so that it
         is possible to qualify the symbols of the current modules. *)
      loaded := Path.Map.add mp sign !loaded;
      Tactic.reset_admitted();
      let compile = compile_with ~handle ~force in
      let consume cmd = Stdlib.(sig_st := handle compile !sig_st cmd) in
      Debug.stream_iter consume (Parser.parse_file src);
      Sign.strip_private sign;
      if Stdlib.(!gen_obj) then begin
        Console.out 1 "Write \"%s\" ..." obj; Sign.write sign obj
      end;
      loading := List.tl !loading;
      Console.out 2 "Checked \"%s\"" src;
      begin
        match !loading with
        | p::_ -> Console.out 2 "Continue checking %a ..." Path.pp p
        | [] -> ()
      end;
      sign
    end
    else
    begin
      Console.out 1 "Load \"%s\" ..." obj;
      let sign = Sign.read obj in
      (* We recursively load every module [mp'] on which [mp] depends. *)
      let compile mp' _ = ignore (compile_with ~handle ~force:false mp') in
      Path.Map.iter compile !(sign.sign_deps);
      loaded := Path.Map.add mp sign !loaded;
      Sign.link sign;
      (* Since ghost signatures are always assumed to be already loaded,
         we need to explicitly update the decision tree of their symbols
         because it is not done in linking which normally follows loading. *)
      Ghost.iter (fun s -> Tree.update_dtree s []);
      sign
    end

(** [compile force mp] compiles module path [mp], forcing
    compilation of up-to-date files if [force] is true. *)
let compile : ?force:bool -> Path.t -> Sign.t = fun ?(force=false) ->
  compile_with ~handle:Command.handle ~force

(** [compile_file fname] looks for a package configuration file for
    [fname] and compiles [fname]. It is the main compiling function. It
    is called from the main program exclusively. *)
let compile_file : ?force:bool -> string -> Sign.t =
  fun ?(force=false) fname ->
  Package.apply_config fname;
  compile ~force (path_of_file LpLexer.escape fname)

(** The functions provided in this module perform the same computations as the
   ones defined earlier, but restore the console state and the library
   mappings when they have finished. An optional library mapping or console
   state can be passed as argument to change the settings. *)
module PureUpToSign = struct

  (** [apply_cfg ?lm ?st f x] is the same as [f x] except that the console
     state and {!val:Library.lib_mappings} are restored after the evaluation
     of [f x]. [?lm] allows to set the library mappings and [?st] to set the
     console state. *)
  let apply_cfg :
    ?lm:Path.t*string -> ?st:Console.State.t -> ('a -> 'b) -> 'a -> 'b =
    fun ?lm ?st f x ->
      let lib_mappings = !Library.lib_mappings in
      Console.State.push ();
      Option.iter Library.add_mapping lm;
      Option.iter Console.State.apply st;
      let restore () =
        Library.lib_mappings := lib_mappings;
        Console.State.pop ()
      in
      try let res = f x in restore (); res
      with e -> restore (); raise e

  let compile :
  ?lm:Path.t*string -> ?st:Console.State.t -> ?force:bool -> Path.t -> Sign.t
    = fun ?lm ?st ?(force=false) -> apply_cfg ?lm ?st (compile ~force)

  let compile_file :
  ?lm:Path.t*string -> ?st:Console.State.t -> ?force:bool -> string -> Sign.t
    = fun ?lm ?st ?(force=false) -> apply_cfg ?lm ?st (compile_file ~force)

end
