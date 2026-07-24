(** Check that failures inside a proof report the proof state: the error
    message stays the bare reason, and the state is attached as the
    [err_desc] of the [Fatal] exception (printed after the message). *)

(** [compile file] compiles [file], restoring the [Timed] state afterwards
    even when compilation fails (otherwise the library-root mapping of a
    failed compilation leaks into the next one). *)
let compile : string -> unit = fun file ->
  let t = Timed.Time.save () in
  Fun.protect ~finally:(fun () -> Timed.Time.restore t)
    (fun () -> ignore (Handle.Compile.compile_file file))

(** [contains s sub] tells whether [sub] occurs in [s]. *)
let contains : string -> string -> bool = fun s sub ->
  let n = String.length sub and m = String.length s in
  let rec loop i = i + n <= m && (String.sub s i n = sub || loop (i + 1)) in
  loop 0

(** [check_error file ~reason ~in_desc ~not_in_desc ()] compiles [file],
    expecting a [Fatal] whose message contains [reason] but no proof state,
    and whose description contains every string of [in_desc] and none of
    [not_in_desc]. *)
let check_error :
  string -> reason:string -> in_desc:string list -> not_in_desc:string list
  -> unit -> unit =
  fun file ~reason ~in_desc ~not_in_desc () ->
  match compile file with
  | _ -> Alcotest.fail (file ^ " should fail to compile")
  | exception Common.Error.Fatal(_, msg, desc) ->
      Alcotest.(check bool) ("message contains: " ^ reason)
        true (contains msg reason);
      Alcotest.(check bool) "message does not embed the proof state"
        false (contains msg "Proof state");
      List.iter
        (fun frag ->
          Alcotest.(check bool) ("description contains: " ^ frag)
            true (contains desc frag))
        in_desc;
      List.iter
        (fun frag ->
          Alcotest.(check bool) ("description does not contain: " ^ frag)
            false (contains desc frag))
        not_in_desc

let sep = "------"

let _ =
  (* Set library root to avoid creating files out of the sandbox when opam
     runs tests. *)
  Common.Library.set_lib_root (Some (Sys.getcwd ()));
  let open Alcotest in
  run "proof_state"
    [ ( "proof_state",
        [ test_case "tactic failure" `Quick
            (check_error "KO/proof_state_fail.lp"
               ~reason:"Call to tactic \"fail\"."
               ~in_desc:
                 [ "Proof state before tactic application:";
                   "a: π A"; "b: π B"; sep; "0. ?" ]
               ~not_in_desc:["Proof state after tactic application:"]);
          test_case "subproof mismatch" `Quick
            (check_error "KO/proof_state_mismatch.lp"
               ~reason:"Missing subproofs (0 subproofs for 2 subgoals)."
               ~in_desc:
                 [ "Proof state before tactic application:";
                   "Proof state after tactic application:";
                   "π (Q z)"; "π (Q (succ x0))" ]
               ~not_in_desc:[]);
          test_case "unfinished proof" `Quick
            (check_error "KO/proof_state_unfinished.lp"
               ~reason:"The proof is not finished."
               ~in_desc:["Proof state:"; "a: π A"; sep; "0. ?"]
               ~not_in_desc:[]) ] ) ]
