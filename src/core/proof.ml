(** Proofs and tactics. *)

open! Lplib
open Lplib.Base

open Timed
open Terms
open Print
open Console
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
        let t, n = Ctxt.to_prod c Type in fst (Env.destruct_prod n t)
    | Typ gt -> gt.goal_hyps

  (** [of_meta m] creates a goal from the meta [m]. *)
  let of_meta : meta -> goal = fun m ->
    let (goal_hyps, goal_type) =
      Env.destruct_prod m.meta_arity !(m.meta_type) in
    let goal_type = Eval.simplify (Env.to_ctxt goal_hyps) goal_type in
    Typ {goal_meta = m; goal_hyps; goal_type}

  (** [simpl g] normalizes the goal [g]. *)
  let simpl : goal -> goal = fun g ->
    match g with
    | Typ gt ->
        let goal_type =  Eval.snf (Env.to_ctxt gt.goal_hyps) gt.goal_type in
        Typ {gt with goal_type}
    | Unif (c,t,u) -> Unif (c, Eval.snf c t, Eval.snf c u)

  (** Comparison function. Unification goals are greater than typing goals. *)
  let compare : goal cmp = fun g g' ->
    match g, g' with
    | Typ gt, Typ gt' -> (* Smaller (= older) metas are put first. *)
        Meta.compare gt.goal_meta gt'.goal_meta
    | Unif c, Unif c' -> Basics.cmp_constr c c'
    | Unif _, Typ _ -> 1
    | Typ _, Unif _ -> -1

  (** [pp oc g] prints on channel [oc] the goal [g] without its hypotheses. *)
  let pp : goal pp = fun oc g ->
    let out fmt = Format.fprintf oc fmt in
    match g with
    | Typ gt -> out "%a: %a\n" pp_meta gt.goal_meta pp_term gt.goal_type
    | Unif (_, t, u) -> out "%a ≡ %a\n" pp_term t pp_term u

  (** [pp_hyps oc g] prints on channel [oc] the hypotheses of the goal [g]. *)
  let pp_hyps : goal pp =
    let env_elt oc (s,(_,t,_)) =
      Format.fprintf oc "%s: %a\n" s pp_term (Bindlib.unbox t)
    in
    let ctx_elt oc (x,a,t) =
      Format.fprintf oc "%a: %a" pp_var x pp_term a;
      match t with
      | None -> Format.fprintf oc "\n"
      | Some(t) -> Format.fprintf oc " ≔ %a\n" pp_term t
    in
    let hyps hyp oc l =
      if l <> [] then
        (List.iter (hyp oc) (List.rev l);
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
  let f = function Typ gt -> Some gt.goal_meta.meta_key | Unif _ -> None in
  let metakeys_gs = List.filter_rev_map f gs in
  let add_goal m goals =
    if List.mem m.meta_key metakeys_gs then goals
    else List.insert Goal.compare (Goal.of_meta m) goals
  in
  MetaSet.fold add_goal ms [] @ gs

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
      List.iteri (fun i g -> out "%d. %a" i Goal.pp g) ps.proof_goals

(** [focus_env ps] returns the scoping environment of the focused goal or the
   empty environment if there is none. *)
let focus_env : proof_state option -> Env.t = fun ps ->
  match ps with
  | None -> Env.empty
  | Some(ps) ->
      match ps.proof_goals with
      | [] -> Env.empty
      | g::_ -> Goal.env g

(** [goals_of_typ typ ter] returns a list of goals for [typ] to be typable by
   by a sort and [ter] to have type [typ] in the empty context. [ter] and
   [typ] must not be both equal to [None]. *)
let goals_of_typ : popt -> term option -> term option -> goal list * term =
  fun pos typ ter ->
  let (typ, to_solve) =
    match typ, ter with
    | Some(typ), Some(ter) ->
        begin
          match Infer.infer_noexn [] [] typ with
          | None -> fatal pos "[%a] is not typable." pp_term typ
          | Some(sort, to_solve) ->
              let to_solve =
                match unfold sort with
                | Type | Kind ->
                    begin
                      match Infer.check_noexn to_solve [] ter typ with
                      | None -> fatal pos "[%a] cannot have type [%a]"
                                  pp_term ter pp_term typ
                      | Some cs -> cs
                    end
                | _ -> fatal pos "[%a] has type [%a] and not a sort."
                         pp_term typ pp_term sort
              in
              typ, to_solve
        end
    | None, Some(ter) ->
        begin
          match Infer.infer_noexn [] [] ter with
          | None -> fatal pos "[%a] is not typable." pp_term ter
          | Some (typ, to_solve) ->
              let to_solve =
                match unfold typ with
                | Kind -> fatal pos "Kind definitions are not allowed."
                | _ ->
                    match Infer.infer_noexn to_solve [] typ with
                    | None ->
                        fatal pos "[%a] has type [%a] which is not typable"
                          pp_term ter pp_term typ
                    | Some (sort, to_solve) ->
                        match unfold sort with
                        | Type | Kind -> to_solve
                        | _ ->
                            fatal pos
                              "[%a] has type [%a] which has type [%a] \
                               and not a sort."
                              pp_term ter pp_term typ pp_term sort
              in
              typ, to_solve
        end
    | Some(typ), None ->
        begin
          match Infer.infer_noexn [] [] typ with
          | None -> fatal pos "[%a] is not typable." pp_term typ
          | Some (sort, to_solve) ->
              match unfold sort with
              | Type | Kind -> typ, to_solve
              | _ -> fatal pos "[%a] has type [%a] and not a sort."
                       pp_term typ pp_term sort
        end
    | None, None -> assert false (* already rejected by parser *)
  in
  (List.rev_map (fun c -> Unif c) to_solve, typ)
