(** Proofs and tactics. *)

open Lplib open Base open Extra
open Timed
open Core open Term open Print
open Common open Pos

(** Type of goals. *)
type goal_typ =
  { goal_meta : meta  (** Goal metavariable. *)
  ; goal_hyps : Env.t (** Precomputed scoping environment. *)
  ; goal_type : term  (** Precomputed type. *) }

type goal =
  | Typ of goal_typ (** Typing goal. *)
  | Unif of constr (** Unification goal. *)

let is_typ : goal -> bool = function Typ _ -> true  | Unif _ -> false
let is_unif : goal -> bool = function Typ _ -> false | Unif _ -> true

let get_constr : goal -> constr =
  function Unif c -> c | Typ _ -> invalid_arg (__FILE__ ^ "get_constr")

let get_names : goal -> StrSet.t = function
  | Unif(c,_,_) -> Ctxt.names c
  | Typ gt -> Env.names gt.goal_hyps

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
      let t, n = Ctxt.to_prod c mk_Type in
      (try fst (Env.of_prod_nth c n t)
       with Invalid_argument _ -> assert false)
    | Typ gt -> gt.goal_hyps

  (** [of_meta m] creates a goal from the meta [m]. *)
  let of_meta : meta -> goal = fun m ->
    let goal_hyps, goal_type =
      try Env.of_prod_nth [] m.meta_arity !(m.meta_type)
      with Invalid_argument _ -> assert false
    in Typ {goal_meta = m; goal_hyps; goal_type}

  (** [simpl f g] simplifies the goal [g] with the function [f]. *)
  let simpl : (ctxt -> term -> term) -> goal -> goal = fun f g ->
    match g with
    | Typ gt ->
        Typ {gt with goal_type = f (Env.to_ctxt gt.goal_hyps) gt.goal_type}
    | Unif (c,t,u) -> Unif (c, f c t, f c u)

  (** [hyps ppf g] prints on [ppf] the hypotheses of the goal [g]. *)
  let hyps : StrSet.t -> goal pp =
    let hyps elt ppf l =
      if l <> [] then
        out ppf "@[<v>%a@,\
        -----------------------------------------------\
        ---------------------------------@,@]"
        (List.pp (fun ppf -> out ppf "%a@," elt) "") (List.rev l);

    in
    fun ids ppf g ->
    let term = term_in ids in
    match g with
    | Typ gt ->
      let elt ppf (s,(_,t,u)) =
        match u with
        | None -> out ppf "%a: %a" uid s term t
        | Some u -> out ppf "%a ≔ %a" uid s term u
      in
      hyps elt ppf gt.goal_hyps
    | Unif (c,_,_) ->
      let elt ppf (x,a,t) =
        out ppf "%a: %a" var x term a;
        match t with
        | None -> ()
        | Some t -> out ppf " ≔ %a" term t
      in
      hyps elt ppf c

  let pp_aux : StrSet.t -> goal pp = fun ids ppf g ->
    let term = term_in ids in
    match g with
    | Typ gt -> out ppf "%a: %a" meta gt.goal_meta term gt.goal_type
    | Unif (_, t, u) -> out ppf "%a ≡ %a" term t term u

  (** [pp ppf g] prints on [ppf] the goal [g] with its hypotheses. *)
  let pp ppf g = let ids = get_names g in hyps ids ppf g; pp_aux ids ppf g

  (** [pp_aux ppf g] prints on [ppf] the goal [g] without its hypotheses. *)
  let pp_no_hyp ppf g = let ids = get_names g in pp_aux ids ppf g
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
  | g::gs ->
      let goal ppf i g = out ppf "%d. %a@," (i+1) Goal.pp_no_hyp g in
      let goals ppf = List.iteri (goal ppf) in
      out ppf "@[<v>%a%a@]" Goal.pp g goals gs

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
