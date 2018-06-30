(** Main program. *)

open Console
open Files

(** [compile fname] compiles the source file [fname]. *)
let compile : string -> unit = fun fname ->
  try Handle.compile true (module_path fname) with Fatal(popt,msg) ->
    begin
      match popt with
      | None    -> Format.eprintf (red "%s\n") msg
      | Some(p) -> Format.eprintf (red "[%a] %s\n") Pos.print p msg
    end;
    exit 1

(* Main program. *)
let _ =
  let justparse = ref false in
  let debug_doc =
    let flags = List.map (fun s -> String.make 20 ' ' ^ s)
      [ (* in alphabetical order *)
        "a : general debug informations"
      ; "c : extra debugging informations for metavariables"
      ; "e : extra debugging informations for equality"
      ; "m : extra debugging informations for matching"
      ; "p : extra debugging informations for the parser"
      ; "r : extra debugging informations for evaluation"
      ; "s : extra debugging informations for subject reduction"
      ; "t : extra debugging informations for typing"
      ; "u : extra debugging informations for unification"
      ]
    in "<str> Enable debugging modes:\n" ^ String.concat "\n" flags
  in
  let verbose_doc =
    let flags = List.map (fun s -> String.make 20 ' ' ^ s)
      [ "0 (or less) : no output at all"
      ; "1 : only file loading information (default)"
      ; "2 : more file loading information"
      ; "3 (or more) : show the results of commands" ]
    in "<int> Set the verbosity level:\n" ^ String.concat "\n" flags
  in
  let gen_obj_doc = " Produce object files (\".dko\" extension)" in
  let too_long_doc = "<flt> Duration considered too long for a command" in
  let onlyparse_doc = " Only parse the input files (no type-checking)" in
  let earleylvl_doc = "<int> Sets the internal debugging level of Earley" in
  let spec =
    [ ("--gen-obj"  , Arg.Set Handle.gen_obj          , gen_obj_doc  )
    ; ("--toolong"  , Arg.Float ((:=) Handle.too_long), too_long_doc )
    ; ("--verbose"  , Arg.Int ((:=) verbose)          , verbose_doc  )
    ; ("--justparse", Arg.Set justparse               , onlyparse_doc)
    ; ("--earleylvl", Arg.Int ((:=) Earley.debug_lvl) , earleylvl_doc)
    ; ("--debug"    , Arg.String (set_debug true)     , debug_doc    ) ]
  in
  let files = ref [] in
  let anon fn = files := fn :: !files in
  let summary =
    " [--debug [a|r|u|m|s|t|e|p]] [--verbose N] [--gen-obj] [FILE] ..."
  in
  Arg.parse (Arg.align spec) anon (Sys.argv.(0) ^ summary);
  if !justparse then
    List.iter (fun f -> ignore (Parser.parse_file f)) !files
  else
    List.iter compile (List.rev !files);
  if !debug_pars then
    wrn "Total time spent in parsing: %.2f seconds.\n" !Parser.total_time
