(** Set option for files *)

open File_management.Pos
open File_management.Error

open Why3_tactic

(** [handle_set_option q] *)
let handle_set_option : Parsing.Syntax.p_set_option -> 'a = fun q ->
  match q.elt with
  | P_set_option_debug(e,s) ->
      (* Just update the option, state not modified. *)
      set_debug e s; out 3 "(flag) debug → %s%s\n" (if e then "+" else "-") s;
  | P_set_option_verbose(i) ->
      (* Just update the option, state not modified. *)
      if Timed.(!verbose) = 0 then
        (Timed.(verbose := i); out 1 "(flag) verbose → %i\n" i)
      else
        (out 1 "(flag) verbose → %i\n" i; Timed.(verbose := i));
  | P_set_option_flag(id,b) ->
      (* We set the value of the flag, if it exists. *)
      (try set_flag id b
       with Not_found -> wrn q.pos "Unknown flag \"%s\"." id);
      out 3 "(flag) %s → %b\n" id b;
  | P_set_option_prover(s) ->
      Timed.(default_prover := s);
  | P_set_option_prover_timeout(n) ->
      Timed.(timeout := n);
