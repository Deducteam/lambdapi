(** Proofs and tactics. *)

open! Lplib
open Lplib.Base

open Timed
open Terms
open Print
open Console
open Pos

(** Abstract representation of a goal. *)
module Goal =
  struct
    (** Representation of a proof type goal. *)
    type goal_typ =
      { goal_meta : meta  (* Metavariable needing instantiation.          *)
      ; goal_hyps : Env.t (* Precomputed scope for a suitable term.       *)
      ; goal_type : term  (* Precomputed type for a suitable term.        *) }

    (** [get_meta g] returns the metavariable associated to goal [g]. *)
    let get_meta : goal_typ -> meta = fun g -> g.goal_meta

    (** [get_type g] returns the environment and expected type of the goal. *)
    let get_type : goal_typ -> Env.t * term = fun g ->
      (g.goal_hyps, g.goal_type)

    (** [goal_typ_of_meta m] create a goal from the metavariable [m]. *)
    let goal_typ_of_meta : meta -> goal_typ = fun m ->
      let (goal_hyps, goal_type) =
        Env.destruct_prod m.meta_arity !(m.meta_type)
      in
      let goal_type = Eval.simplify (Env.to_ctxt goal_hyps) goal_type in
      {goal_meta = m; goal_hyps; goal_type}

    (** [simpl g] simplifies the given goal, evaluating its type to SNF. *)
    let simpl : goal_typ -> goal_typ = fun g ->
      {g with goal_type = Eval.snf (Env.to_ctxt g.goal_hyps) g.goal_type}

    (** Representation of a general goal : type, unification *)
    type t =
      | Typ of goal_typ (* The usual proof type goal. *)
      | Unif of constr (* Two terms we'd like equal in ctxt. *)

    (** Helper functions *)
    let is_typ  = function Typ _ -> true  | Unif _ -> false
    let is_unif = function Typ _ -> false | Unif _ -> true
    let typ = function x -> Typ x
    let unif = function x -> Unif x
    let get_goal_typ = function Typ gt -> gt | _ -> invalid_arg __LOC__
    let get_constr = function Unif c -> c | _ -> invalid_arg __LOC__
    let of_meta m = Typ (goal_typ_of_meta m)

    (** Comparison function. *)
    let compare : t cmp = fun g g' ->
      match g, g' with
      | Typ gt, Typ gt' -> Meta.compare gt.goal_meta gt'.goal_meta
      | Unif c, Unif c' -> Basics.cmp_constr c c'
      | Unif _, Typ _ -> 1
      | Typ _, Unif _ -> -1

  end

(** [goals_of_metas ms] returns a list of goals from a set of metas. *)
let goals_of_metas : MetaSet.t -> Goal.t list = fun ms ->
  let add_goal m = List.insert Goal.compare (Goal.of_meta m) in
  MetaSet.fold add_goal ms []

(** Representation of the proof state of a theorem. *)
type proof_state =
  { proof_name     : strloc  (** Name of the theorem.                 *)
  ; proof_term     : meta option (** Optional metavariable holding the goal
                                     associated to a symbol used as a
                                     theorem/definition and not just a
                                     simple declaration *)
  ; proof_goals    : Goal.t list (** Open goals (focused goal is first).  *) }

(** Short synonym for qualified use. *)
type t = proof_state

(** [goals_of_typ typ ter] returns a list of goals for [typ] to be typable by
   by a sort and [ter] to have type [typ] in the empty context. [ter] and
   [typ] must not be both equal to [None]. *)
let goals_of_typ : popt -> term option -> term option -> Goal.t list * term =
  fun pos typ ter ->
  let (typ, to_solve) =
    match typ, ter with
    | Some(typ), Some(ter) ->
        begin
          match Infer.infer_noexn [] typ with
          | None -> fatal pos "[%a] is not typable." pp_term typ
          | Some(sort, to_solve1) ->
              let to_solve2 =
                match unfold sort with
                | Type | Kind ->
                    begin
                      match Infer.check_noexn [] ter typ with
                      | None -> fatal pos "[%a] cannot have type [%a]"
                                  pp_term ter pp_term typ
                      | Some cs -> cs
                    end
                | _ -> fatal pos "[%a] has type [%a] and not a sort."
                         pp_term typ pp_term sort
              in
              typ, to_solve1 @ to_solve2
        end
    | None, Some(ter) ->
        begin
          match Infer.infer_noexn [] ter with
          | None -> fatal pos "[%a] is not typable." pp_term ter
          | Some (typ, to_solve2) ->
              let to_solve1 =
                match unfold typ with
                | Kind -> fatal pos "Kind definitions are not allowed."
                | _ ->
                    match Infer.infer_noexn [] typ with
                    | None ->
                        fatal pos "[%a] has type [%a] which is not typable"
                          pp_term ter pp_term typ
                    | Some (sort, to_solve1) ->
                        match unfold sort with
                        | Type | Kind -> to_solve1
                        | _ ->
                            fatal pos
                              "[%a] has type [%a] which has type [%a] \
                               and not a sort."
                              pp_term ter pp_term typ pp_term sort
              in
              typ, to_solve1 @ to_solve2
        end
    | Some(typ), None ->
        begin
          match Infer.infer_noexn [] typ with
          | None -> fatal pos "[%a] is not typable." pp_term typ
          | Some (sort, to_solve) ->
              match unfold sort with
              | Type | Kind -> typ, to_solve
              | _ -> fatal pos "[%a] has type [%a] and not a sort."
                       pp_term typ pp_term sort
        end
    | None, None -> assert false (* already rejected by parser *)
  in
  (List.map Goal.unif to_solve, typ)

(** [finished ps] tells whether there are unsolved goals in [ps]. *)
let finished : t -> bool = fun ps -> ps.proof_goals = []

(** [focus_goal ps] returns the focused goal or fails if there is none. *)
let focus_goal : popt -> proof_state -> Env.t * term = fun pos ps ->
  match List.hd ps.proof_goals with
    | Goal.Typ g -> Goal.get_type g
    | Goal.Unif _ -> fatal pos "No remaining typing goals ..."
    | exception Failure(_) -> fatal pos "No remaining goals ..."

(** [pp_goals oc gl] prints the goal list [gl] to channel [oc]. *)
let pp_goals : proof_state pp = fun oc ps ->
  match ps.proof_goals with
  | []    -> Format.fprintf oc " No more goals...\n"
  | g::gs ->
    Format.fprintf oc "\n== Goals ================================\n";
    match g with
    | Goal.Typ g ->
      let (hyps, a) = Goal.get_type g in
      if hyps <> [] then
        begin
          let print_hyp (s,(_,t,_)) =
            Format.fprintf oc "   %s : %a\n" s pp_term (Bindlib.unbox t)
          in
          List.iter print_hyp (List.rev hyps);
          Format.fprintf oc "   --------------------------------------\n"
        end;
      Format.fprintf oc "Typ  0. %a (precomputed %a)\n"
        Print.pp_meta g.goal_meta pp_term a;
      if gs <> [] then
        begin
          Format.fprintf oc "\n";
          let print_goal i g =
            match g with
            | Goal.Typ g ->
              let (_, a) = Goal.get_type g in
              Format.fprintf oc "Typ  %i. %a (precomputed %a)\n"
                (i+1) Print.pp_meta g.goal_meta pp_term a
            | Goal.Unif cs ->
              Format.fprintf oc "Unif %i. %a\n" (i+1) pp_constr cs
          in
          List.iteri print_goal gs
        end
    | Goal.Unif cs -> Format.fprintf oc "Unif 0. %a\n" pp_constr cs;
      if gs <> [] then
        begin
          Format.fprintf oc "\n";
          let print_goal i g =
            match g with
            | Goal.Typ g ->
              let (_, a) = Goal.get_type g in
              Format.fprintf oc "Typ  %i. %a (precomputed %a)\n"
                (i+1) Print.pp_meta g.goal_meta pp_term a
            | Goal.Unif cs ->
              Format.fprintf oc "Unif %i. %a\n"
                (i+1) pp_constr cs
          in
          List.iteri print_goal gs
        end
