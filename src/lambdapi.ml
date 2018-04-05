(** Main program. *)

open Console
open Files
open Sign

(* [compile fname] compiles the source file [fname]. *)
let compile : string -> unit = fun fname ->
  let modpath = module_path fname in
  current_state := new_state modpath;
  Handle.compile true modpath

(* Main program. *)
let _ =
  let debug_doc =
    let flags = List.map (fun s -> String.make 20 ' ' ^ s)
      [ "a : general debug informations"
      ; "e : extra debugging informations for evaluation"
      ; "u : extra debugging informations for unification"
      ; "p : extra debugging informations for patterns"
      ; "t : extra debugging informations for typing"
      ; "q : extra debugging informations for equality" ]
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
  let wrn_no_ta_doc = " Warn the user when abstractions are not annotated" in
  let spec =
    [ ("--debug"        , Arg.String (set_debug true), debug_doc    )
    ; ("--verbose"      , Arg.Int ((:=) verbose)     , verbose_doc  )
    ; ("--gen-obj"      , Arg.Set Handle.gen_obj     , gen_obj_doc  )
    ; ("--warn-no-annot", Arg.Set Scope.wrn_no_type  , wrn_no_ta_doc) ]
  in
  let files = ref [] in
  let anon fn = files := fn :: !files in
  let summary =
    " [--debug [a|e|u|p|t|q]] [--verbose N] [--gen-obj] [FILE] ..."
  in
  Arg.parse (Arg.align spec) anon (Sys.argv.(0) ^ summary);
  List.iter compile (List.rev !files)
