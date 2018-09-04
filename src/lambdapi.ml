(** Main program. *)

open Extra
open Console
open Files
open Legacy_parser

(** Timeout for compilation (in seconds). *)
let timeout : int option Pervasives.ref = Pervasives.ref None

let set_timeout : int -> unit = fun i ->
  if i <= 0 then
    begin
      Format.eprintf (red "Invalid timeout value.\n");
      exit 1
    end;
  timeout := Some(i)

(** [compile fname] compiles the source file [fname]. *)
let compile : string -> unit = fun fname ->
  let compile = Handle.compile true in
  let run () =
    let mp = module_path fname in
    match !timeout with
    | None    -> compile mp
    | Some(i) -> with_timeout i compile mp
  in
  try run () with
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
  let gen_obj_doc = " Produce object files (\".dko\" extension)" in
  let too_long_doc = "<flt> Duration considered too long for a command" in
  let onlyparse_doc = " Only parse the input files (no type-checking)" in
  let earleylvl_doc = "<int> Sets the internal debugging level of Earley" in
  let legacy_doc = " Use the legacy parser (faster, but old syntax only)" in
  let timeout_doc = "<int> Use a timeout of the given number of seconds" in
  let spec =
    [ ("--gen-obj"      , Arg.Set Handle.gen_obj          , gen_obj_doc  )
    ; ("--toolong"      , Arg.Float ((:=) Handle.too_long), too_long_doc )
    ; ("--verbose"      , Arg.Int (Timed.(:=) verbose)    , verbose_doc  )
    ; ("--justparse"    , Arg.Set justparse               , onlyparse_doc)
    ; ("--earleylvl"    , Arg.Int ((:=) Earley.debug_lvl) , earleylvl_doc)
    ; ("--legacy-parser", Arg.Set Handle.use_legacy_parser, legacy_doc   )
    ; ("--timeout"      , Arg.Int set_timeout             , timeout_doc  )
    ; ("--debug"        , Arg.String (set_debug true)     , debug_doc    ) ]
  in
  let files = Pervasives.ref [] in
  let anon fn = Pervasives.(files := fn :: !files) in
  Arg.parse (Arg.align spec) anon (Sys.argv.(0) ^ " [OPTIONS] [FILES]");
  if !justparse then
    let parse_file fname =
      if !Handle.use_legacy_parser then Legacy_parser.parse_file fname
      else Parser.parse_file fname
    in
    List.iter (fun f -> ignore (parse_file f)) !files
  else
    List.iter compile (List.rev !files);
  Parser.log_pars "Total time in parsing: %.2f seconds.\n" !Parser.total_time
