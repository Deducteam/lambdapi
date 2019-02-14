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
        let rec aux n t acc =
          if n = 0 then (acc, t) else
          match t with
          | Prod(a,b) ->
              let (v,b) = Bindlib.unbind b in
              aux (n-1) b ((Bindlib.name_of v,(v,lift a))::acc)
          | _         -> assert false
        in
        aux m.meta_arity !(m.meta_type) []
      in
      {goal_meta = m; goal_hyps; goal_type}

    let get_meta : t -> meta = fun g -> g.goal_meta

    let get_type : t -> Env.t * term = fun g -> (g.goal_hyps, g.goal_type)

    let simpl : t -> t = fun g -> {g with goal_type = Eval.snf g.goal_type}
  end

(** Representation of the state of the proof of a theorem. *)
type proof =
  { proof_name     : Pos.strloc  (** Name of the theorem.                 *)
  ; proof_term     : meta        (** Metavariable holding the proof term. *)
  ; proof_goals    : Goal.t list (** Open goals (focused goal is first).  *)
  ; proof_builtins : builtins    (** Signature state, for builtins.       *) }

and builtins = (sym * pp_hint) StrMap.t

(** Short synonym for qualified use. *)
type t = proof

(** [init builtins name a] returns an initial proof state for a theorem  named
    [name], which statement is represented by the type [a]. Builtin symbols of
    [builtins] may be used by tactics, and have been declared. *)
let init : builtins -> Pos.strloc -> term -> t = fun proof_builtins name a ->
  let proof_term = fresh_meta ~name:name.elt a 0 in
  let proof_goals = [Goal.of_meta proof_term] in
  {proof_name = name; proof_term; proof_goals; proof_builtins}

(** [finished ps] tells whether the proof represented by [ps] is finished. *)
let finished : t -> bool = fun ps -> ps.proof_goals = []

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

(** [pp oc ps] prints the proof state [ps] to channel [oc]. *)
let pp : t pp = fun oc ps ->
  Format.fprintf oc "== Current theorem ======================\n";
  pp_goals oc ps.proof_goals;
  Format.fprintf oc "==========================================\n"
