(** Proofs and tactics. *)

open! Lplib
open Base
open Extra
open Timed
open Core
open Term
open Print
open Common
open Error
open Pos

(** Type of goals. *)
type goal_typ =
  { goal_meta : meta  (* Goal metavariable. *)
  ; goal_hyps : Env.t (* Precomputed scoping environment. *)
  ; goal_type : term  (* Precomputed type. *) }

type goal =
  | Typ of goal_typ
  (** Typing goal. *)
  | Unif of constr
  (** Unification goal. *)

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
        let t, n = Ctxt.to_prod c Type in fst (Env.of_prod c n t)
    | Typ gt -> gt.goal_hyps

  (** [of_meta m] creates a goal from the meta [m]. *)
  let of_meta : meta -> goal = fun m ->
    let (goal_hyps, goal_type) = Env.of_prod [] m.meta_arity !(m.meta_type) in
    let goal_type = Eval.simplify goal_type in
    Typ {goal_meta = m; goal_hyps; goal_type}

  (** [simpl f g] simplifies the goal [g] with the function [f]. *)
  let simpl : (term -> term) -> goal -> goal = fun f g ->
    match g with
    | Typ gt -> Typ {gt with goal_type = f gt.goal_type}
    | Unif (c,t,u) -> Unif (c, f t, f u)

  (** Comparison function. Unification goals are greater than typing goals. *)
  let compare : goal cmp = fun g g' ->
    match g, g' with
    | Typ gt, Typ gt' -> (* Smaller (= older) metas are put first. *)
        Meta.compare gt.goal_meta gt'.goal_meta
    | Unif c, Unif c' -> LibTerm.cmp_constr c c'
    | Unif _, Typ _ -> 1
    | Typ _, Unif _ -> -1

  (** [pp oc g] prints on channel [oc] the goal [g] without its hypotheses. *)
  let pp : goal pp = fun oc g ->
    let out fmt = Format.fprintf oc fmt in
    match g with
    | Typ gt -> out "%a: %a" pp_meta gt.goal_meta pp_term gt.goal_type
    | Unif (_, t, u) -> out "%a ≡ %a" pp_term t pp_term u

  (** [pp_hyps oc g] prints on channel [oc] the hypotheses of the goal [g]. *)
  let pp_hyps : goal pp =
    let env_elt oc (s,(_,t,_)) =
      Format.fprintf oc "%a: %a" pp_uid s pp_term (Bindlib.unbox t)
    in
    let ctx_elt oc (x,a,t) =
      Format.fprintf oc "%a: %a" pp_var x pp_term a;
      match t with
      | None -> ()
      | Some(t) -> Format.fprintf oc " ≔ %a" pp_term t
    in
    let hyps hyp oc l =
      if l <> [] then
        (List.iter (Format.fprintf oc "%a\n" hyp) (List.rev l);
         Format.fprintf oc "-----------------------------------------------\
                            ---------------------------------\n")
    in
    fun oc g ->
    match g with
    | Typ gt -> hyps env_elt oc gt.goal_hyps
    | Unif (c,_,_) -> hyps ctx_elt oc c

end

(** [add_goals_of_metas ms gs] extends [gs] with the metas of [ms] that are
   not already in [gs]. *)
let add_goals_of_metas : MetaSet.t -> goal list -> goal list = fun ms gs ->
  (* computes the metas of [gs]. *)
  let metas =
    let add_meta metas g =
      match g with
      | Typ gt -> MetaSet.add gt.goal_meta metas
      | _ -> metas
    in
    List.fold_left add_meta MetaSet.empty gs
  in
  (* [add_meta_to_goals m gs] inserts the meta [m] into the list of goals
     [gs], assuming that [gs] is sorted wrt [Goal.compare], if [m] is
     uninstantiated and does not belong to the set of metas [metas]. Do
     nothing otherwise. *)
  let add_meta_to_goals m gs =
    if !(m.meta_value) <> None || MetaSet.mem m metas then gs
    else List.insert Goal.compare (Goal.of_meta m) gs
  in
  MetaSet.fold add_meta_to_goals ms [] @ gs

(** Representation of the proof state of a theorem. *)
type proof_state =
  { proof_name  : strloc (** Name of the theorem. *)
  ; proof_term  : meta option
  (** Optional metavariable holding the goal associated to a symbol used as a
     theorem/definition and not just a simple declaration *)
  ; proof_goals : goal list (** Open goals (focused goal is first). *) }

(** [finished ps] tells whether there are unsolved goals in [ps]. *)
let finished : proof_state -> bool = fun ps -> ps.proof_goals = []

(** [pp_goals oc gl] prints the goal list [gl] to channel [oc]. *)
let pp_goals : proof_state pp = fun oc ps ->
  let out fmt = Format.fprintf oc fmt in
  match ps.proof_goals with
  | [] -> out "No goals.\n"
  | g::_ ->
      out "\n";
      Goal.pp_hyps oc g;
      List.iteri (fun i g -> out "%d. %a\n" i Goal.pp g) ps.proof_goals

(** [remove_solved_goals ps] removes from the proof state [ps] the typing
   goals that are solved. *)
let remove_solved_goals : proof_state -> proof_state = fun ps ->
  let f = function
    | Typ gt -> !(gt.goal_meta.meta_value) = None
    | Unif _ -> true
  in {ps with proof_goals = List.filter f ps.proof_goals}

(** [sys_metas ps] returns the map of system-generated metavariables of the
   proof state [ps]. *)
let sys_metas : proof_state -> meta IntMap.t = fun ps ->
  let f sgm goal =
    match goal with
    | Typ {goal_meta=m;_} when m.meta_name = None ->
        IntMap.add m.meta_key m sgm
    | _ -> sgm
  in
  List.fold_left f IntMap.empty ps.proof_goals

(** [focus_env ps] returns the scoping environment of the focused goal or the
   empty environment if there is none. *)
let focus_env : proof_state option -> Env.t = fun ps ->
  match ps with
  | None -> Env.empty
  | Some(ps) ->
      match ps.proof_goals with
      | [] -> Env.empty
      | g::_ -> Goal.env g

(** [goals_of_typ typ ter] returns a triplet [(cs, ty, te)] where [cs] is the
    list of unification goals that must be solved so that [typ] is typable by
    a sort and [ter] has type [typ] and [ty] (respectively [te]) is the
    refinement of [typ] (resp. [ter]). *)
let goals_of_typ : term loc option -> term loc option ->
  goal list * term * term option =
  fun typ ter ->
  let module Infer = (val Stdlib.(!Infer.default)) in
  let (ter, typ, to_solve) =
    match typ, ter with
    | Some(typ), Some(ter) ->
        begin
          match Infer.infer_noexn [] [] typ.elt with
          | None -> fatal typ.pos "[%a] is not typable." pp_term typ.elt
          | Some(ty, sort, to_solve) ->
              let to_solve, te =
                match unfold sort with
                | Type | Kind ->
                    begin
                      match Infer.check_noexn to_solve [] ter.elt ty with
                      | None ->
                          let pos = Common.Pos.cat typ.pos ter.pos in
                          fatal pos "[%a] cannot have type [%a]"
                            pp_term ter.elt pp_term ty
                      | Some (te, cs) -> (cs, te)
                    end
                | _ -> fatal typ.pos "[%a] has type [%a] and not a sort."
                         pp_term ty pp_term sort
              in
              Some te, ty, to_solve
        end
    | None, Some(ter) ->
        begin
          match Infer.infer_noexn [] [] ter.elt with
          | None -> fatal ter.pos "[%a] is not typable." pp_term ter.elt
          | Some (te, ty, to_solve) ->
              let to_solve =
                match unfold ty with
                | Kind -> fatal ter.pos "Kind definitions are not allowed."
                | _ ->
                    match Infer.infer_noexn to_solve [] ty with
                    | None ->
                        fatal ter.pos
                          "[%a] has type [%a] which is not typable"
                          pp_term te pp_term ty
                    | Some (_, sort, to_solve) ->
                        match unfold sort with
                        | Type | Kind -> to_solve
                        | _ ->
                            fatal ter.pos
                              "[%a] has type [%a] which has type [%a] \
                               and not a sort."
                              pp_term te pp_term ty pp_term sort
              in
              Some te, ty, to_solve
        end
    | Some(typ), None ->
        begin
          match Infer.infer_noexn [] [] typ.elt with
          | None -> fatal typ.pos "[%a] is not typable." pp_term typ.elt
          | Some (ty, sort, to_solve) ->
              match unfold sort with
              | Type | Kind -> None, ty, to_solve
              | _ -> fatal typ.pos "[%a] has type [%a] and not a sort."
                       pp_term ty pp_term sort
        end
    | None, None -> assert false (* already rejected by parser *)
  in
  (List.map (fun c -> Unif c) to_solve, typ, ter)

(** [goals_of_typ typ ter] returns a 3-uple [(gs, ty, te)] where [gs] is a
    list of goals for [typ] to be typable by a sort and [ter] to have type
    [typ] in the empty context. [ter] and [typ] must not be both equal to
    [None] and are refined into [te] and [ty] respectively. NOTE:
    [goals_of_typ typ ter] contains typing goals to type [typ] by a sort and
    unification goals to type both [typ] by a sort and [ter] by [typ]. However
    it does not contain typing goals to type [ter] by [typ]. These goals are
    generated using the {!constructor:Handle.Tactic.tac_refine} tactic called
    on [ter]. *)
let goals_of_typ : term loc option -> term loc option ->
  goal list * term * term option =
  fun typ ter ->
  let metas = match typ with
    | Some ty -> LibTerm.Meta.get true ty.elt
    | None -> MetaSet.empty
  in
  let proof_goals, typ, ter = goals_of_typ typ ter in
  add_goals_of_metas metas proof_goals, typ, ter
