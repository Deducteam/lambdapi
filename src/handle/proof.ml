(** Proofs and tactics. *)

open Lplib open Base
open Timed
open Core open Term open Print
open Common open Pos

(** Type of goals. *)
type goal_typ =
  { goal_meta : meta  (* Goal metavariable. *)
  ; goal_hyps : Env.t (* Precomputed scoping environment. *)
  ; goal_type : term  (* Precomputed type. *) }

type goal =
  | Typ of goal_typ (** Typing goal. *)
  | Unif of constr (** Unification goal. *)

let is_typ : goal -> bool = function Typ _ -> true  | Unif _ -> false
let is_unif : goal -> bool = function Typ _ -> false | Unif _ -> true
let get_constr : goal -> constr =
  function Unif c -> c | Typ _ -> invalid_arg (__FILE__ ^ "get_constr")

module Goal = struct

  type t = goal

  (** [ctxt g] returns the typing context of the goal [g]. *)
  let ctxt : goal -> ctxt = fun g ->
    match g with
    | Typ gt -> Env.to_ctxt gt.goal_hyps
    | Unif (c,_,_) -> c

  (** [env g] returns the scoping environment of the goal [g]. *)
  let env : goal -> Env.t = fun g ->
    match g with
    | Unif (c,_,_) ->
        let t, n = Ctxt.to_prod c mk_Type in fst (Env.of_prod_nth c n t)
    | Typ gt -> gt.goal_hyps

  (** [of_meta m] creates a goal from the meta [m]. *)
  let of_meta : meta -> goal = fun m ->
    let goal_hyps, goal_type =
      (*let s = Format.asprintf "%s, of_meta %a(%d):%a" __LOC__
                meta m m.meta_arity term !(m.meta_type) in*)
      Env.of_prod_nth [] m.meta_arity !(m.meta_type) in
    Typ {goal_meta = m; goal_hyps; goal_type}

  (** [simpl f g] simplifies the goal [g] with the function [f]. *)
  let simpl : (term -> term) -> goal -> goal = fun f g ->
    match g with
    | Typ gt -> Typ {gt with goal_type = f gt.goal_type}
    | Unif (c,t,u) -> Unif (c, f t, f u)

  (** [pp ppf g] prints on [ppf] the goal [g] without its hypotheses. *)
  let pp : goal pp = fun ppf g ->
    match g with
    | Typ gt -> out ppf "%a: %a" meta gt.goal_meta term gt.goal_type
    | Unif (_, t, u) -> out ppf "%a ≡ %a" term t term u

  (** [hyps ppf g] prints on [ppf] the hypotheses of the goal [g]. *)
  let hyps : goal pp =
    let env_elt ppf (s,(_,t,_)) = out ppf "%a: %a" uid s term t in
    let ctx_elt ppf (x,a,t) =
      out ppf "%a: %a" var x term a;
      match t with
      | None -> ()
      | Some t -> out ppf " ≔ %a" term t
    in
    let hyps hyp ppf l =
      if l <> [] then
        out ppf "@[<v>%a@,\
        -----------------------------------------------\
        ---------------------------------@,@]"
        (List.pp (fun ppf -> out ppf "%a@," hyp) "") (List.rev l);

    in
    fun ppf g ->
    match g with
    | Typ gt -> hyps env_elt ppf gt.goal_hyps
    | Unif (c,_,_) -> hyps ctx_elt ppf c

end

(** [add_goals_of_problem p gs] extends the list of goals [gs] with the
   metavariables and constraints of [p]. *)
let add_goals_of_problem : problem -> goal list -> goal list = fun p gs ->
  let gs = MetaSet.fold (fun m gs -> Goal.of_meta m :: gs) !p.metas gs in
  let f gs c = Unif c :: gs in
  let gs = List.fold_left f gs !p.to_solve in
  List.fold_left f gs !p.unsolved

(** Representation of the proof state of a theorem. *)
type proof_state =
  { proof_name  : strloc (** Name of the theorem. *)
  ; proof_term  : meta option
  (** Optional metavariable holding the goal associated to a symbol used as a
     theorem/definition and not just a simple declaration *)
  ; proof_goals : goal list (** Open goals (focused goal is first). *) }

(** [finished ps] tells whether there are unsolved goals in [ps]. *)
let finished : proof_state -> bool = fun ps -> ps.proof_goals = []

(** [goals ppf gl] prints the goal list [gl] to channel [ppf]. *)
let goals : proof_state pp = fun ppf ps ->
  match ps.proof_goals with
  | [] -> out ppf "No goals."
  | g::_ ->
      out ppf "@[<v>%a%a@]" Goal.hyps g
        (fun ppf -> List.iteri (fun i g -> out ppf "%d. %a@," i Goal.pp g))
        ps.proof_goals

(** [remove_solved_goals ps] removes from the proof state [ps] the typing
   goals that are solved. *)
let remove_solved_goals : proof_state -> proof_state = fun ps ->
  let f = function
    | Typ gt -> !(gt.goal_meta.meta_value) = None
    | Unif _ -> true
  in {ps with proof_goals = List.filter f ps.proof_goals}

(** [meta_of_key ps i] returns [Some m] where [m] is a meta of [ps] whose key
   is [i], or else it returns [None]. *)
let meta_of_key : proof_state -> int -> meta option = fun ps key ->
  let f = function
    | Typ {goal_meta=m;_} when m.meta_key = key -> Some m
    | _ -> None
  in
  List.find_map f ps.proof_goals

(** [focus_env ps] returns the scoping environment of the focused goal or the
   empty environment if there is none. *)
let focus_env : proof_state option -> Env.t = fun ps ->
  match ps with
  | None -> Env.empty
  | Some(ps) ->
      match ps.proof_goals with
      | [] -> Env.empty
      | g::_ -> Goal.env g
