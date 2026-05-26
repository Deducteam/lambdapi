(** High-level compilation functions. *)

open Lplib
open Timed
open Common open Error open Library
open Parsing
open Core open Sign

(** [gen_obj] indicates whether we should generate object files when compiling
    source files. The default behaviour is not te generate them. *)
let gen_obj = Stdlib.ref false

(** [compile force] returns a compiler, i.e. a function of type [Path.t ->
    Sign.t]. [compile force mp] returns the signature associated to the module
    path [mp]. The corresponding file is processed only when the corresponding
    object file does not exist or must be updated, or when [~force] is
    [true]. In that case, the produced signature is stored in the
    corresponding object file if the option [--gen_obj] or [-c] is set. *)
let rec compile : bool -> Command.compiler = fun force mp ->
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
      Console.out 1 (Color.blu "Start checking \"%s\"%s") src forced;
      loading := mp :: !loading;
      let sign = Sign.create mp in
      let ss = Stdlib.ref (Sig_state.of_sign sign) in
      (* [sign] is added to [loaded] before processing the commands so that it
         is possible to qualify the symbols of the current modules. *)
      loaded := Path.Map.add mp sign !loaded;
      (*let open Base in sout "loaded:";
        Path.Map.iter (fun p _ -> sout " %a" Path.pp p) !loaded;
        sout "\n%!";*)
      Tactic.reset_admitted();
      let consume cmd =
        Stdlib.(ss := Command.handle (compile force) !ss cmd) in
      Debug.stream_iter consume (Parser.parse_file src);
      Console.out 1 (Color.blu "End checking \"%s\"%s") src forced;
      Sign.strip_private sign;
      if Stdlib.(!gen_obj) then begin
        Console.out 2 (Color.blu "Writing \"%s\" ...")obj; Sign.write sign obj
      end;
      loading := List.tl !loading;
      sign
    end
    else
    begin
      Console.out 2 (Color.blu "Loading \"%s\" ...") obj;
      let sign = Sign.read obj in
      (* We recursively load every module [mp'] on which [mp] depends. *)
      let compile mp _ = ignore (compile false mp) in
      Path.Map.iter compile !(sign.sign_deps);
      loaded := Path.Map.add mp sign !loaded;
      Sign.link sign;
      (* Since ghost signatures are always assumed to be already loaded,
         we need to explicitly update the decision tree of their symbols
         because it is not done in linking which normally follows loading. *)
      Ghost.iter (fun s -> Tree.update_dtree s []);
      sign
    end

let compile = compile false

(** [compile_file fname] looks for a package configuration file for [fname]
    and compiles [fname]. *)
let compile_file (fname:string): Sign.t =
  Package.apply_config fname;
  compile (path_of_file LpLexer.escape fname)
