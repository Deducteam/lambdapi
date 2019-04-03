(** Proofs and tactics. *)

open Timed
open Extra
open Pos
open Terms

(** Abstract representation of a goal. *)
module Goal :
  sig
    (** Representation of a goal. *)
    type t

    (** [of_meta m] create a goal from the metavariable [m]. *)
    val of_meta : meta -> t

    (** [get_meta g] returns the metavariable associated to goal [g]. *)
    val get_meta : t -> meta

    (** [get_type g] returns the environment and expected type of the goal. *)
    val get_type : t -> Env.t * term

    (** [simpl g] simplifies the given goal, evaluating its type to SNF. *)
    val simpl : t -> t
  end =
  struct
    type t =
      { goal_meta : meta  (* Metavariable needing instantiation.    *)
      ; goal_hyps : Env.t (* Precomputed scope for a suitable term. *)
      ; goal_type : term  (* Precomputed type for a suitable term.  *) }

    let of_meta : meta -> t = fun m ->
      let (goal_hyps, goal_type) =
        Env.of_prod_arity m.meta_arity !(m.meta_type) in
      let goal_type = Eval.simpl_beta goal_type in
      {goal_meta = m; goal_hyps; goal_type}

    let get_meta : t -> meta = fun g -> g.goal_meta

    let get_type : t -> Env.t * term = fun g -> (g.goal_hyps, g.goal_type)

    let simpl : t -> t = fun g -> {g with goal_type = Eval.snf g.goal_type}
  end

(** Representation of the proof state of a theorem. *)
type proof_state =
  { proof_name     : Pos.strloc  (** Name of the theorem.                 *)
  ; proof_term     : meta        (** Metavariable holding the proof term. *)
  ; proof_goals    : Goal.t list (** Open goals (focused goal is first).  *)
  ; proof_builtins : sym StrMap.t(** Signature state, for builtins.       *) }

(** Short synonym for qualified use. *)
type t = proof_state

(** [init builtins name a] returns an initial proof state for a theorem  named
    [name], which statement is represented by the type [a]. Builtin symbols of
    [builtins] may be used by tactics, and have been declared. *)
let init : sym StrMap.t -> Pos.strloc -> term -> t =
  fun proof_builtins name a ->
  let proof_term = fresh_meta ~name:name.elt a 0 in
  let proof_goals = [Goal.of_meta proof_term] in
  {proof_name = name; proof_term; proof_goals; proof_builtins}

(** [finished ps] tells whether the proof represented by [ps] is finished. *)
let finished : t -> bool = fun ps -> ps.proof_goals = []

(** [focus_goal ps] returns the focused goal or fails if there is none. *)
let focus_goal : proof_state -> Env.t * term = fun ps ->
  try Goal.get_type (List.hd ps.proof_goals)
  with Failure(_)  -> Console.fatal_no_pos "No remaining goals..."

(** [pp_goals oc gl] prints the goal list [gl] to channel [oc]. *)
let pp_goals : _ pp = fun oc gl ->
  let open Print in
  match gl with
  | []    -> Format.fprintf oc " No more goals...\n"
  | g::gs ->
    let (hyps, a) = Goal.get_type g in
    let print_hyp (s,(_,t)) =
      Format.fprintf oc "  %s : %a\n" s pp (Bindlib.unbox t)
    in
    List.iter print_hyp (List.rev hyps);
    Format.fprintf oc " ----------------------------------------\n";
    Format.fprintf oc "  %a\n" pp a;
    if gs <> [] then
      begin
        let g_meta = Goal.get_meta g in
        let (_, g_type) = Goal.get_type g in
        Format.fprintf oc "\n";
        Format.fprintf oc " >0< %a : %a\n" pp_meta g_meta pp g_type;
        let print_goal i g =
          let m = Goal.get_meta g in
          let (_, a) = Goal.get_type g in
          Format.fprintf oc " (%i) %a : %a\n" (i+1) pp_meta m pp a
        in
        List.iteri print_goal gs
      end

(** [pp oc ps] prints the proof state [ps] to channel [oc]. *)
let pp : t pp = fun oc ps ->
  Format.fprintf oc "== Current theorem ======================\n";
  pp_goals oc ps.proof_goals;
  Format.fprintf oc "=========================================\n"
