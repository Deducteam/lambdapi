open Common
open Handle

let () =
  (* Set library root to avoid creating files out of the sandbox when
     opam runs tests. *)
  Library.set_lib_root (Some (Sys.getcwd ()))

(** Sanity check for pure compilation: same file may be compiled twice. *)
let test_compile_twice () =
  let nat_lp = "OK/nat.lp" in
  ignore @@ Compile.Pure.compile_file nat_lp;
  Alcotest.(check unit) "Compile twice same file in same runtime"
   (ignore @@ Compile.Pure.compile_file nat_lp) ()

(** Check that pure compilation is indeed pure. *)
let purity_check () =
  let open Timed in
  let libmap = !Library.lib_mappings in
  let verbose = !Console.verbose in
  let loggers = Logger.get_activated_loggers () in
  let flags = Stdlib.(!Console.boolean_flags) in
  ignore @@ Compile.Pure.compile_file "OK/nat.lp";
  Alcotest.(check int) "verbosity" verbose !Console.verbose;
  Alcotest.(check string) "loggers" loggers (Logger.get_activated_loggers ());
  (* The pretty printer is used to check equality *)
  Alcotest.(check (of_pp Library.LibMap.pp)) "libmaps" libmap !Library.lib_mappings;
  let check_flag fl (v,dv) =
    let (v',dv') = Lplib.Extra.StrMap.find fl flags in
    assert (v = v');
    assert (!dv = !dv')
  in
  Alcotest.(check unit) "boolean flags"
    (Lplib.Extra.StrMap.iter check_flag Stdlib.(!Console.boolean_flags)) ()

let () =
  let open Alcotest in
  run "Purity"
    [ "properties of compilation"
    , [ test_case "compiling twice" `Quick test_compile_twice
      ; test_case "state unchanged" `Quick purity_check ] ]

