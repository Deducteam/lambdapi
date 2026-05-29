(** High-level compilation functions. *)

open Lplib
open Timed
open Common open Error open Library
open Parsing
open Core open Sign

(** [gen_obj] indicates whether we should generate object files when compiling
    source files. The default behaviour is not te generate them. *)
let gen_obj = Stdlib.ref false

(** [source base] returns which file among [base.dk] and [base.lp] to use. *)
let source base =
  let lp_src = base ^ lp_src_extension
  and dk_src = base ^ dk_src_extension in
  match Sys.file_exists lp_src, Sys.file_exists dk_src with
  | false, false ->
      fatal_no_pos "File \"%s.lp\" (or .dk) not found." base
  | true , true ->
      wrn None "Both \"%s\" and \"%s\" exist. We take \"%s\"."
        lp_src dk_src lp_src; lp_src
  | true , false -> lp_src
  | false, true -> dk_src

(** [compile ss mp] returns the signature associated to the module path
    [mp]. The corresponding file is processed only when the corresponding
    object file does not exist or must be updated. In that case, the signature
    is stored in the corresponding object file if [!gen_obj] is [true]. The
    sig_state [ss] is only used to get the "String" builtin. *)
let rec compile : Command.compiler = fun ss mp ->
  if List.mem mp !loading then
    begin
      let base = file_of_path mp in
      fatal_msg "Circular dependency detected in \"%s\".@." (source base);
      fatal_msg "Dependency stack for module:@.";
      List.iter (fatal_msg "- %a@." Path.pp) !loading;
      fatal_no_pos "Build aborted."
    end;
  if mp = Ghost.path then Ghost.sign else
  match Path.Map.find_opt mp !loaded with
  | Some sign -> sign
  | None ->
    let base = file_of_path mp in
    let obj = base ^ obj_extension in
    let src = source base in
    if Extra.more_recent src obj then
    begin
      Console.out 1 (Color.blu "Start checking \"%s\"") src;
      loading := mp :: !loading;
      let sign = Sign.create mp in
      (* [sign] is added to [loaded] before processing the commands so that it
         is possible to qualify the symbols of the current modules. *)
      loaded := Path.Map.add mp sign !loaded;
      (*let open Base in sout "loaded:";
        Path.Map.iter (fun p _ -> sout " %a" Path.pp p) !loaded;
        sout "\n%!";*)
      Tactic.reset_admitted();
      let ss = Stdlib.ref (Elpi_handle.Sig_state.of_sign sign) in
      let consume cmd = Stdlib.(ss := Command.handle compile !ss cmd) in
      Debug.stream_iter consume (Parser.parse_file src);
      Console.out 1 (Color.blu "End checking \"%s\"") src;
      Sign.strip_private sign;
      if Stdlib.(!gen_obj) then begin
        Console.out 2 (Color.blu "Write \"%s\"") obj;
        Sign.write sign obj
      end;
      loading := List.tl !loading;
      sign
    end
    else
    begin
      Console.out 2 (Color.blu "Load \"%s\"") obj;
      let sign = Sign.read obj in
      (* We recursively load every module [mp'] on which [mp] depends. *)
      Path.Map.iter (fun mp' _ -> ignore (compile ss mp')) !(sign.sign_deps);
      loaded := Path.Map.add mp sign !loaded;
      Sign.link sign;
      (* Since the ghost signature is implicitly loaded but not linked, we
         need to explicitly update the decision tree of ghost symbols and the
         type of string literals with the String builtin. *)
      let update s =
        if String.is_string_literal s.Term.sym_name then
          match Extra.StrMap.find_opt "String" !(sign.sign_builtins) with
          | Some sym_String -> s.sym_type := Term.mk_Symb sym_String
          | None ->
          match Builtin.get_opt ss "String" with
          | Some sym_String -> s.sym_type := Term.mk_Symb sym_String
          | None -> assert false
        else Tree.update_dtree s []
      in
      Ghost.iter update;
      sign
    end

(** [compile_file fname] looks for a package configuration file for [fname]
    and compiles [fname]. *)
let compile_file (fname:string): Sign.t =
  Package.apply_config fname;
  compile Elpi_handle.Sig_state.dummy (path_of_file LpLexer.escape fname)
