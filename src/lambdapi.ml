(** Main program. *)

open Extra
open Console
open Files

(** [confluence_checker] holds a possible confluence checking command. When it
    is given, the command should accept TPDB format on its input and the first
    line of its output yould contain either ["YES"], ["NO"] or ["MAYBE"]. *)
let confluence_checker : string option Pervasives.ref = Pervasives.ref None

(** [set_confluence cmd] sets the confluence checker command to [cmd]. *)
let set_confluence : string -> unit = fun cmd ->
  Pervasives.(confluence_checker := Some(cmd))

(** [timeout] holds a possible timeout for compilation (in seconds). *)
let timeout : int option Pervasives.ref = Pervasives.ref None

(** [set_timeout i] sets a timeout of [i] seconds on the compilation. *)
let set_timeout : int -> unit = fun i ->
  if i <= 0 then (Format.eprintf (red "Invalid timeout value.\n"); exit 1);
  timeout := Some(i)

(** [use_legacy_parser] indicates whether the legacy (Menhir) parser should be
    used. It is faster, but only supports the legacy syntax. *)
let use_legacy_parser = Pervasives.ref false

let parse_file : string -> Syntax.p_cmd Pos.loc list = fun fname ->
  let new_syntax = Filename.check_suffix fname new_src_extension in
  let parse =
    match (new_syntax, !use_legacy_parser) with
    | (true , _    ) -> New_parser.parse_file
    | (false, true ) -> Legacy_parser.parse_file
    | (false, false) -> Parser.parse_file
  in
  parse fname

(** [compile fname] compiles the source file [fname]. *)
let compile : string -> unit = fun fname ->
  let mp = module_path fname in
  let old = Filename.check_suffix fname src_extension in
  let compile = Handle.new_compile old parse_file true in
  let run () =
    match !timeout with
    | None    -> compile mp
    | Some(i) -> with_timeout i compile mp
  in
  try
    run ();
    match !confluence_checker with
    | None      -> ()
    | Some(cmd) ->
        let sign = PathMap.find mp Sign.(Timed.(!loaded)) in
        match Confluence.check cmd sign with
        | None     -> fatal_no_pos "The rewrite system may not be confluent."
        | Some(ok) -> if not ok then
                        fatal_no_pos "The rewrite system is not confluent."
  with
  | Fatal(popt,msg) ->
      begin
        match popt with
        | None    -> Format.eprintf (red "%s\n") msg
        | Some(p) -> Format.eprintf (red "[%a] %s\n") Pos.print p msg
      end;
      exit 1
  | Timeout         ->
      Format.eprintf (red "[%s] Compilation timed out.\n") fname;
      exit 1

(* Main program. *)
let _ =
  let justparse = Pervasives.ref false in
  let padding = String.make 8 ' ' in
  let debug_doc =
    let flags = Console.log_summary () in
    let flags = List.map (fun s -> padding ^ s) flags in
    "<str> Sets the given debugging flags.\n      Available flags:\n"
    ^ String.concat "\n" flags
  in
  let verbose_doc =
    let flags = List.map (fun s -> padding ^ s)
      [ "0 (or less) : no output at all"
      ; "1 : only file loading information (default)"
      ; "2 : more file loading information"
      ; "3 (or more) : show the results of commands" ]
    in
    "<int> Set the verbosity level.\n      Available values:\n"
    ^ String.concat "\n" flags
  in
  let cc_doc = "<cmd> Runs the given confluence checker" in
  let gen_obj_doc = " Produce object files (\".dko\" extension)" in
  let too_long_doc = "<flt> Duration considered too long for a command" in
  let onlyparse_doc = " Only parse the input files (no type-checking)" in
  let earleylvl_doc = "<int> Sets the internal debugging level of Earley" in
  let legacy_doc = " Use the legacy parser (faster, but old syntax only)" in
  let timeout_doc = "<int> Use a timeout of the given number of seconds" in
  let spec = List.sort (fun (f1,_,_) (f2,_,_) -> String.compare f1 f2)
    [ ("--gen-obj"      , Arg.Set Handle.gen_obj          , gen_obj_doc  )
    ; ("--toolong"      , Arg.Float ((:=) Handle.too_long), too_long_doc )
    ; ("--verbose"      , Arg.Int (Timed.(:=) verbose)    , verbose_doc  )
    ; ("--justparse"    , Arg.Set justparse               , onlyparse_doc)
    ; ("--earleylvl"    , Arg.Int ((:=) Earley.debug_lvl) , earleylvl_doc)
    ; ("--legacy-parser", Arg.Set use_legacy_parser       , legacy_doc   )
    ; ("--timeout"      , Arg.Int set_timeout             , timeout_doc  )
    ; ("--confluence"   , Arg.String set_confluence       , cc_doc       )
    ; ("--debug"        , Arg.String (set_debug true)     , debug_doc    ) ]
  in
  let files = Pervasives.ref [] in
  let anon fn = Pervasives.(files := fn :: !files) in
  Arg.parse (Arg.align spec) anon (Sys.argv.(0) ^ " [OPTIONS] [FILES]");
  if !justparse then
    let parse_file fname =
      if Filename.check_suffix fname src_extension then
        if !use_legacy_parser then
          ignore (Legacy_parser.parse_file fname)
        else
          ignore (Parser.parse_file fname)
      else
        ignore (New_parser.parse_file fname)
    in
    List.iter parse_file !files
  else
    List.iter compile (List.rev !files)
