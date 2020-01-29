(** Main program. *)

open Core
open Extra
open Files
open Console

(* NOTE only standard [Pervasives] references here. *)

(** [confluence_checker] holds a possible confluence checking command. When it
   is given, the command should accept the HRS format on its input (see
   http://project-coco.uibk.ac.at/problems/hrs.php) and the first line of its
   output should contain either ["YES"], ["NO"] or ["MAYBE"]. *)
let confluence_checker : string option ref = ref None

(** [termination_checker] holds a possible termination checking command, using
   a similar mechanism as for [confluence_checker]. The command should accept
   XTC format on its input (see
   http://cl2-informatik.uibk.ac.at/mercurial.cgi/TPDB/file/tip/xml/xtc.xsd),
   and the first line of its output should contain either ["YES"], ["NO"] or
   ["MAYBE"]. *)
let termination_checker : string option ref = ref None

(** Available modes for handling input files. *)
type execution_mode =
  | Normal    (** Type-checking (default mode).     *)
  | JustParse (** Only parse the files.             *)
  | Beautify  (** Parse and pretty-print the files. *)
  | LSP       (** Run the LSP server.               *)

(** [mode] holds the chosen exectuion mode for the run. *)
let mode = ref Normal

(** [timeout] holds a possible timeout for compilation (in seconds). *)
let timeout : int option ref = ref None

(** [handle_file fname] handles (i.e., processes) the file [fname] taking care
    of pottential errors in the process. *)
let handle_file : string -> unit = fun fname ->
  try
    (* Handle non-normal modes first. *)
    match !mode with
    | LSP       -> fatal_no_pos "LSP server does not expect file arguments."
    | JustParse -> ignore (Compile.parse_file fname)
    | Beautify  -> Pretty.beautify (Compile.parse_file fname)
    | Normal    ->
    (* Compute the module path (checking the extension). *)
    let mp = Files.file_to_module fname in
    (* Run the compilation, possibly using a timeout. *)
    let compile = Compile.compile true in
    let _ =
      match !timeout with
      | None    -> compile mp
      | Some(i) -> try with_timeout i compile mp with Timeout ->
                     fatal_no_pos "Compilation timed out for [%s]." fname
    in
    let run_checker prop fn chk kw =
      let run cmd =
        let sign = PathMap.find mp Sign.(Timed.(!loaded)) in
          match External.run prop fn cmd sign with
          | Some(true ) -> ()
          | Some(false) -> fatal_no_pos "The rewrite system is not %s." kw
          | None        -> fatal_no_pos "The rewrite system may not be %s." kw
      in
      Option.iter run !chk
    in
    run_checker "confluence" Hrs.to_HRS confluence_checker "confluent";
    run_checker "termination" Xtc.to_XTC termination_checker "terminating"
  with
  | Fatal(None,    msg) -> exit_with "%s" msg
  | Fatal(Some(p), msg) -> exit_with "[%a] %s" Pos.print p msg

(** [spec] contains the command line argument specification. *)
let spec =
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
      , Arg.Set Compile.gen_obj
      , Printf.sprintf " Produce object files (%S extension)" obj_extension )
    ; ( "--no-color"
      , Arg.Set Console.color
      , " Do not use colors in the output" )
    ; ( "--write-trees"
      , Arg.Set Handle.write_trees
      , " Write decision trees to \".gv\" files" )
    ; ( "--keep-rule-order"
      , Arg.Set Tree.rule_order
      , " Respect the order of definition of the rewriting rules" )
    ; ( "--too-long"
      , Arg.Float ((:=) Handle.too_long)
      , "<float> Duration considered too long for a command" )
    ; ( "--verbose"
      , Arg.Int set_default_verbose
      , "<int> Set the default verbosity level" ^ verbose_values )
    ; ( "--no-warnings"
      , Arg.Unit (fun _ -> no_wrn := true)
      , " Disables the printing of warnings" )
    ; ( "--just-parse"
      , Arg.Unit (fun _ -> mode := JustParse)
      , " Only parse the input files (no type-checking)" )
    ; ( "--beautify"
      , Arg.Unit (fun _ -> mode := Beautify; set_default_verbose 0)
      , " Parse input files and pretty-print them (in the new syntax)" )
    ; ( "--timeout"
      , Arg.Int set_timeout
      , "<int> Use a timeout of the given number of seconds" )
    ; ( "--confluence"
      , Arg.String (fun cmd -> confluence_checker := Some(cmd))
      , "<cmd> Runs the given confluence checker" )
    ; ( "--termination"
      , Arg.String (fun cmd -> termination_checker := Some(cmd))
      , "<cmd> Runs the given termination checker" )
    ; ( "--lib-root"
      , Arg.String Files.set_lib_root
      , Printf.sprintf "<path> sets the library root (default is \"%s\")"
          (Files.default_lib_root ()) )
    ; ( "--map"
      , Arg.String Files.new_lib_mapping
      , "<modpath>:<path> maps the given path under the library root" )
    ; ( "--version"
      , Arg.Unit (fun () -> out 0 "Lambdapi %s\n%!" Version.version; exit 0)
      , " Prints the current version number and exits" )
    ; ( "--debug"
      , Arg.String set_default_debug
      , "<flags> Enables given debugging flags by default " ^ debug_flags )
    ; ( "--lsp-server"
      , Arg.Unit (fun _ -> mode := LSP)
      , " Start the LSP server" )
    ; ( "--standard-lsp"
      , Arg.Set Lsp.Lp_lsp.use_standard_lsp
      , " Restrict to standard LSP protocol" )
    ; ( "--lsp-log-file"
      , Arg.Set_string Lsp.Lp_lsp.log_file
      , "<file> Specified the LSP server log file (default: "
          ^ Lsp.Lp_lsp.default_log_file ^ ")" ) ]
  in
  List.sort (fun (f1,_,_) (f2,_,_) -> String.compare f1 f2) spec

(** Main program. *)
let _ =
  (* Parse command line arguments while accumulating all files. *)
  let usage = Printf.sprintf "Usage: %s [OPTIONS] [FILES]" Sys.argv.(0) in
  let files = ref [] in
  Arg.parse spec (fun s -> files := s :: !files) usage;
  (* Log some configuration data. *)
  if Timed.(!log_enabled) then
    begin
      Files.log_file "running directory: [%s]" (Files.current_path ());
      Files.log_file "library root path: [%s]" (Files.lib_root_path ());
      let fn = Files.log_file "mapping: [%a] → [%s]" Files.Path.pp in
      Files.ModMap.iter fn (Files.current_mappings ())
    end;
  (* Register the library root. *)
  Files.init_lib_root ();
  (* Compile each file separately. *)
  List.iter handle_file (List.rev !files);
  (* Start the LSP server if appropriate. *)
  if !mode = LSP then Lsp.Lp_lsp.run ()
