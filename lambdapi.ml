(** Main program. *)

open Console
open Files

(* [compile fname] compiles the source file [fname]. *)
let compile : string -> unit = fun fname ->
  let modpath =
    try module_path fname with Invalid_argument _ ->
    fatal "Invalid extension for %S (expected %S)...\n" fname src_extension
  in
  Hashtbl.clear Sign.loaded;
  Cmds.compile true modpath

(* Main program. *)
let _ =
  let debug_doc =
    let flags = List.map (fun s -> String.make 20 ' ' ^ s)
      [ "a : general debug informations"
      ; "e : extra debugging informations for equality"
      ; "i : extra debugging informations for inference"
      ; "p : extra debugging informations for patterns"
      ; "t : extra debugging informations for typing" ]
    in "<str> enable debugging modes:\n" ^ String.concat "\n" flags
  in
  let verbose_doc =
    let flags = List.map (fun s -> String.make 20 ' ' ^ s)
      [ "0 (or less) : no output at all"
      ; "1 : only file loading information (default)"
      ; "2 (or more) : show the results of commands" ]
    in "<int> et the verbosity level:\n" ^ String.concat "\n" flags
  in
  let spec =
    [ ("--debug"  , Arg.String (set_debug true), debug_doc  )
    ; ("--verbose", Arg.Int ((:=) verbose)     , verbose_doc) ]
  in
  let files = ref [] in
  let anon fn = files := fn :: !files in
  let summary = " [--debug [a|e|i|p|t]] [--verbose N] [FILE] ..." in
  Arg.parse (Arg.align spec) anon (Sys.argv.(0) ^ summary);
  List.iter compile (List.rev !files)
