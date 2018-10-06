(** Confluence checking.

    This module allows the translation of a signature in the TPDB format (used
    in the confluence competition. *)

open Extra
open Timed
open Console
open Terms

(** [to_TPDB oc sign] outputs a TPDB representation of the rewriting system of
    the signature [sign] to the output channel [oc]. *)
let to_TPDB : Format.formatter -> Sign.t -> unit = fun oc sign ->
  (* Get all the dependencies (every needed symbols and rewriting rules). *)
  let deps = Sign.dependencies sign in
  (* Function to iterate over every symbols. *)
  let iter_symbols : (sym -> unit) -> unit = fun fn ->
    let iter_symbols sign =
      StrMap.iter (fun _ (s,_) -> fn s) Sign.(!(sign.symbols))
    in
    List.iter (fun (_, sign) -> iter_symbols sign) deps
  in
  (* Print the prelude. *)
  let prelude =
    [ "(FUN"
    ; "  lam  : term -> (term -> term) -> term"
    ; "  app  : term -> term -> term"
    ; "  pi   : term -> (term -> term) -> term"
    ; "  type : term"
    ; ")"
    ; ""
    ; "(COMMENT beta-reduction)"
    ; "(VAR"
    ; "  v_x   : term"
    ; "  m_typ : term"
    ; "  m_B   : term"
    ; "  m_F   : term -> term"
    ; ")"
    ; "(RULES app(lam(m_typ,\\v_x. m_F v_x), m_B) -> m_F(m_B))" ]
  in
  List.iter (Format.fprintf oc "%s\n") prelude;
  (* Print the symbol declarations. *)
  Format.fprintf oc "\n(COMMENT symbols)\n";
  let print_symbol s =
    Format.fprintf oc "(FUN c_%a : term)\n" (Print.pp_symbol Qualified) s
  in
  iter_symbols print_symbol;
  (* Print the rewriting rules. *)
  Format.fprintf oc "\n(COMMENT rewriting rules)\n";
  let print_rules s =
    match !(s.sym_def) with
    | Some(d) ->
        Format.fprintf oc "(RULES ... -> ...)\n"
        (* TODO *)
    | None    ->
        let print_rule r =
          Format.fprintf oc "(RULES ... -> ...)\n"
          (* TODO *)
        in
        List.iter print_rule !(s.sym_rules)
  in
  iter_symbols print_rules

(** [check cmd sign] runs the confluence checker specified by command [cmd] on
    the rewrite system of signature [sign]. The return value is [Some true] in
    the case where the system is confluent.  It is [Some false] if the  system
    is not confluent, and it is [None] if the tool cannot conclude.  Note that
    it is assumed that [cmd] corresponds to a command that accepts TPSP format
    on its standard output, and outputs either ["YES"], ["NO"] or ["MAYBE"] as
    the first line of its standard output. The exception [Fatal] may be raised
    if [cmd] does not behave as expected. *)
let check : string -> Sign.t -> bool option = fun cmd sign ->
  (* Run the command. *)
  let (ic, oc) = Unix.open_process cmd in
  (* Feed it the TPDB problem. *)
  to_TPDB (Format.formatter_of_out_channel oc) sign;
  flush oc;
  (* Read the answer. *)
  let answer = input_line ic in
  (* Terminate the process. *)
  match (Unix.close_process (ic, oc), answer) with
  | (Unix.WEXITED 0, "YES"  ) -> Some true
  | (Unix.WEXITED 0, "NO"   ) -> Some false
  | (Unix.WEXITED 0, "MAYBE") -> None
  | (Unix.WEXITED 0, s      ) ->
      fatal_no_pos "The confluence checker answered [%s]." s
  | (_             , _      ) ->
      fatal_no_pos "The confluence checker unexpectedly failed."

(* NOTE the simplest, valid confluence checking command is ["echo MAYBE"]. The
   command ["echo MAYBE; sponge out.txt"] can be used to output the  generated
   TPDB problem to the file ["out.txt"] for debugging purposes. *)
