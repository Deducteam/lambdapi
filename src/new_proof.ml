(** Proofs and tactics. *)

open Timed
open Extra
open Pos
open Terms
open Console

(** Abstract representation of a goal. *)
module Goal :
  sig
    (** Representation of a goal. *)
    type t

    (** [of_meta m] create a goal from the metavariable [m]. *)
    val of_meta : meta -> t

    (** [of_meta_decomposed m] is similar to [of_meta m] but it decomposes the
        type of [m] for [goal_hyps] and [goal_type]. *)
    val of_meta_decomposed : meta -> t

    (** [get_meta g] returns the metavariable associated to goal [g]. *)
    val get_meta : t -> meta

    (** [get_type g] returns the environment and expected type of the goal. *)
    val get_type : t -> Env.t * term

    (** [simpl g] simlifies the given goal, evaluating its type to SNF. *)
    val simpl : t -> t
  end =
  struct
    type t =
      { goal_meta : meta  (* Metavariable needing instantiation.    *)
      ; goal_hyps : Env.t (* Precomputed scope for a suitable term. *)
      ; goal_type : term  (* Precomputed type for a suitable term.  *) }

    let of_meta : meta -> t = fun goal_meta ->
      {goal_meta; goal_hyps = []; goal_type = !(goal_meta.meta_type)}

    let of_meta_decomposed : meta -> t = fun m ->
      let (goal_hyps, goal_type) =
        Handle.env_of_prod m.meta_arity !(m.meta_type)
      in
      {goal_meta = m; goal_hyps; goal_type}

    let get_meta : t -> meta = fun g -> g.goal_meta

    let get_type : t -> Env.t * term = fun g -> (g.goal_hyps, g.goal_type)

    let simpl : t -> t = fun g -> {g with goal_type = Eval.snf g.goal_type}
  end

(** Representation of the state of the proof of a theorem. *)
type proof =
  { proof_name  : Pos.strloc  (** Name of the proved theorem.            *)
  ; proof_term  : meta        (** Metavariable holding the proof term.   *)
  ; proof_goals : Goal.t list (** List of open goals (focused is first). *) }

(** Short synonym for qualified use. *)
type t = proof

(** [init id a] returns an initial proof state for a theorem named [id], which
    statement is represented by the type [a]. *)
let init : Pos.strloc -> term -> t = fun ({elt=id} as proof_name) a ->
  let proof_term = fresh_meta ~name:id a 0 in
  {proof_name; proof_term; proof_goals = [Goal.of_meta proof_term]}

(** [finished ps] tells whether the proof represented by [ps] is finished. *)
let finished : t -> bool = fun ps -> ps.proof_goals = []

(** [pp oc ps] prints the proof state [ps] to channel [oc]. *)
let pp : t pp = fun oc ps ->
  Format.fprintf oc "== Current theorem ======================\n";
  let open Print in
  begin
    match ps.proof_goals with
    | []    -> Format.fprintf oc " No more goals...\n"
    | g::gs ->
        let (hyps, a) = Goal.get_type g in
        let print_hyp (s,(_,t)) =
          Format.fprintf oc "  %s : %a\n" s pp (Bindlib.unbox t)
        in
        List.iter print_hyp hyps;
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
  end;
  Format.fprintf oc "==========================================\n"
