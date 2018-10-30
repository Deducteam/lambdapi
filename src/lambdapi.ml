(** Main program. *)

open Core
open Extra
open Timed
open Sign
open Console
open Files

(** [confluence_checker] holds a possible confluence checking command. When it
    is given, the command should accept TPDB format on its input and the first
    line of its output yould contain either ["YES"], ["NO"] or ["MAYBE"]. *)
let confluence_checker : string option Pervasives.ref = Pervasives.ref None

(** Available modes for handling input files. *)
type execution_mode =
  | Normal    (** Type-checking (default mode).     *)
  | JustParse (** Only parse the files.             *)
  | Beautify  (** Parse and pretty-print the files. *)

(** [mode] holds the chosen exectuion mode for the run. *)
let mode = Pervasives.ref Normal

(** [timeout] holds a possible timeout for compilation (in seconds). *)
let timeout : int option Pervasives.ref = Pervasives.ref None

(** [gen_obj] indicates whether we should generate object files when compiling
    source files. The default behaviour is not te generate them. *)
let gen_obj = Pervasives.ref false

(** [parse_file fname] selects and runs the correct parser on file [fname], by
    looking at its extension. *)
let parse_file : string -> Syntax.ast = fun fname ->
  match Filename.check_suffix fname new_src_extension with
  | true  -> Parser.parse_file fname
  | false -> Legacy_parser.parse_file fname

(** [compile force path] compiles the file corresponding to [path], when it is
    necessary (the corresponding object file does not exist,  must be updated,
    or [force] is [true]).  In that case,  the produced signature is stored in
    the corresponding object file. *)
let rec compile : bool -> Files.module_path -> unit = fun force path ->
  let base = String.concat "/" path in
  let (src, obj) =
    let new_src = base ^ new_src_extension in
    if Sys.file_exists new_src then (new_src, base ^ new_obj_extension)
    else (base ^ src_extension, base ^ obj_extension)
  in
  if not (Sys.file_exists src) then
    fatal_no_pos "File [%s.{lp|dk}] not found." base;
  if List.mem path !loading then
    begin
      fatal_msg "Circular dependencies detected in [%s].\n" src;
      fatal_msg "Dependency stack for module [%a]:\n" Files.pp_path path;
      List.iter (fatal_msg "  - [%a]\n" Files.pp_path) !loading;
      fatal_no_pos "Build aborted."
    end;
  if PathMap.mem path !loaded then
    out 2 "Already loaded [%s]\n%!" src
  else if force || Files.more_recent src obj then
    begin
      let forced = if force then " (forced)" else "" in
      out 2 "Loading [%s]%s\n%!" src forced;
      loading := path :: !loading;
      let sign = Sign.create path in
      let sig_st = Scope.empty_sig_state sign in
      loaded := PathMap.add path sign !loaded;
      ignore (List.fold_left Handle.handle_cmd sig_st (parse_file src));
      if Pervasives.(!gen_obj) then Sign.write sign obj;
      loading := List.tl !loading;
      out 1 "Checked [%s]\n%!" src;
    end
  else
    begin
      out 2 "Loading [%s]\n%!" src;
      let sign = Sign.read obj in
      PathMap.iter (fun mp _ -> compile false mp) !(sign.sign_deps);
      loaded := PathMap.add path sign !loaded;
      Sign.link sign;
      out 2 "Loaded  [%s]\n%!" obj;
    end

(* Give access to the compilation function to the parser. *)
let _ = Pervasives.(Parser.require := compile false)

(** [handle_file fname] handles (i.e., processes) the file [fname] taking care
    of pottential errors in the process. *)
let handle_file : string -> unit = fun fname ->
  let open Pervasives in
  try
    (* Handle non-normal modes first. *)
    match !mode with
    | JustParse -> ignore (parse_file fname)
    | Beautify  -> Pretty.beautify (parse_file fname)
    | Normal    ->
    (* Compute the module path (checking the extension). *)
    let mp = Files.module_path fname in
    (* Run the compilation, possibly using a timeout. *)
    let compile = compile true in
    let _ =
      match !timeout with
      | None    -> compile mp
      | Some(i) -> try with_timeout i compile mp with Timeout ->
                     fatal_no_pos "Compilation timed out for [%s]." fname
    in
    (* Possibly check the confluence. *)
    match !confluence_checker with
    | None      -> ()
    | Some(cmd) ->
    let sign = Files.PathMap.find mp Sign.(Timed.(!loaded)) in
    match Confluence.check cmd sign with
    | Some(true ) -> ()
    | Some(false) -> fatal_no_pos "The rewrite system is not confluent."
    | None        -> fatal_no_pos "The rewrite system may not be confluent."
  with
  | Fatal(None,    msg) -> exit_with "%s" msg
  | Fatal(Some(p), msg) -> exit_with "[%a] %s" Pos.print p msg

(** [spec] contains the command line argument specification. *)
let spec =
  let open Pervasives in
  let set_timeout : int -> unit = fun i ->
    if i <= 0 then exit_with "Invalid timeout value [%i] (≤ 0)." i;
    timeout := Some(i)
  in
  let debug_flags =
    let fn acc l = acc ^ "\n        " ^ l in
    List.fold_left fn "\n      Available flags:" (Console.log_summary ())
  in
  let verbose_values = "\n" ^ String.concat "\n"
    [ "      Available values:"
    ; "        ≤ 0 : no output at all"
    ; "        = 1 : only file loading information (default)"
    ; "        = 2 : more file loading information"
    ; "        ≥ 3 : show the results of commands" ]
  in
  let spec = Arg.align
    [ ( "--gen-obj"
      , Arg.Set gen_obj
      , " Produce object files (\".dko\" extension)." )
    ; ( "--toolong"
      , Arg.Float ((:=) Handle.too_long)
      , "<flt> Duration considered too long for a command." )
    ; ( "--verbose"
      , Arg.Int (Timed.(:=) verbose)
      , "<int> Set the verbosity level." ^ verbose_values )
    ; ( "--justparse"
      , Arg.Unit (fun _ -> mode := JustParse)
      , " Only parse the input files (no type-checking)." )
    ; ( "--beautify"
      , Arg.Unit (fun _ -> mode := Beautify)
      , " Parse the input files and pretty-print them (in the new syntax)." )
    ; ( "--timeout"
      , Arg.Int set_timeout
      , "<int> Use a timeout of the given number of seconds." )
    ; ( "--confluence"
      , Arg.String (fun cmd -> confluence_checker := Some(cmd))
      , "<cmd> Runs the given confluence checker." )
    ; ( "--debug"
      , Arg.String (set_debug true)
      , "<str> Sets the given debugging flags." ^ debug_flags ) ]
  in
  List.sort (fun (f1,_,_) (f2,_,_) -> String.compare f1 f2) spec

(** Main program. *)
let _ =
  let open Pervasives in
  (* Parse command line arguments while accumulating all files. *)
  let usage = Printf.sprintf "Usage: %s [OPTIONS] [FILES]" Sys.argv.(0) in
  let files = ref [] in
  Arg.parse spec (fun s -> files := s :: !files) usage;
  (* Compile each file separately. *)
  List.iter handle_file (List.rev !files)
