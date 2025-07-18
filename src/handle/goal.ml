(** Goal. *)

open Lplib open Base open Extra
open Timed
open Core open Term open Print

type goal_typ =
  { goal_meta : meta  (** Goal metavariable. *)
  ; goal_hyps : Env.t (** Precomputed scoping environment. *)
  ; goal_type : term  (** Precomputed type. *) }

type ('a,'b) t = Typ of 'a | Unif of 'b

type goal = (goal_typ, constr) t

let is_typ : goal -> bool = function Typ _ -> true  | Unif _ -> false
let is_unif : goal -> bool = function Typ _ -> false | Unif _ -> true

let get_constr : goal -> constr =
  function Unif c -> c | Typ _ -> invalid_arg (__FILE__ ^ "get_constr")

let get_names : goal -> int StrMap.t = function
  | Unif(c,_,_) -> Ctxt.names c
  | Typ gt -> Env.names gt.goal_hyps

(** The string representation of a goal [g] is a tuple [(l,b,s,t)] where [l]
    is a list of pairs of strings [(assumption_name,assumption_type)] and, if
    [g] is a typing goal, then [b=true], [s] is the goal meta name and [t] is
    the goal type, and if [g] is a unification goal, then [b=false] and [s]
    and [t] are the LHS and RHS of the goal respectively. *)
type info = (string * string) list * (string * string, string) t

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
  in
  Typ {goal_meta = m; goal_hyps; goal_type }

(** [simpl_opt f g] tries to simplify the goal [g] with the function [f]. *)
let simpl_opt : (ctxt -> term -> term option) -> goal -> goal option =
  fun f g ->
  match g with
  | Typ gt ->
      begin
        match f (Env.to_ctxt gt.goal_hyps) gt.goal_type with
        | None -> None
        | Some goal_type -> Some(Typ {gt with goal_type})
      end
  | Unif(c,t,u) ->
      match f c t, f c u with
      | Some t, Some u -> Some(Unif(c,t,u))
      | _ -> None

(** [simpl f g] simplifies the goal [g] with the function [f]. *)
let simpl : (ctxt -> term -> term) -> goal -> goal = fun f g ->
  match g with
  | Typ gt ->
      Typ {gt with goal_type = f (Env.to_ctxt gt.goal_hyps) gt.goal_type}
  | Unif (c,t,u) -> Unif (c, f c t, f c u)

(** [hyps ppf g] prints on [ppf] the beta-normal forms of the hypotheses of
    the goal [g]. *)
let hyps : int StrMap.t -> goal pp =
  let hyps elt ppf l =
    if l <> [] then
      out ppf "%a---------------------------------------------\
               ---------------------------------\n"
        (List.pp (fun ppf -> out ppf "%a\n" elt) "") (List.rev l)
  in
  fun idmap ppf g ->
  let term = term_in idmap in
  match g with
  | Typ gt ->
      let elt ppf (s,(_,ty,def)) =
        match def with
        | None -> out ppf "%a: %a" uid s term (Eval.snf_beta ty)
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

(** [concl ppf g] prints on [ppf] the beta-normal form of the conclusion of
    the goal [g]. *)
let concl : int StrMap.t -> goal pp = fun idmap ppf g ->
  let term = term_in idmap in
  match g with
  | Typ gt ->
      out ppf "?%d: %a" gt.goal_meta.meta_key
        term (Eval.snf_beta gt.goal_type)
  | Unif (_, t, u) -> out ppf "%a ≡ %a" term t term u

(** [pp ppf g] prints on [ppf] the beta-normal form of the goal [g] with its
    hypotheses. *)
let pp ppf g = let idmap = get_names g in hyps idmap ppf g; concl idmap ppf g

(** [pp_no_hyp ppf g] prints on [ppf] the beta-normal form of the conclusion
    of the goal [g] without its hypotheses. *)
let pp_no_hyp ppf g = concl (get_names g) ppf g

(** [to_info g] converts the goal [g] into an [info] data structure.*)
let to_info : goal -> info =
  let buf = Buffer.create 80 in
  let ppf = Format.formatter_of_buffer buf in
  let to_string f x =
    f ppf x;
    Format.pp_print_flush ppf ();
    let res = Buffer.contents buf in
    Buffer.clear buf;
    res
  in
  fun g ->
  let term = term_in (get_names g) in
  match g with
  | Typ gt ->
      let env_elt (s,(_,ty,def)) =
        s,
        match def with
        | None -> to_string term (Eval.snf_beta ty)
        | Some d -> "≔ "^to_string term d
      in
      List.rev_map env_elt gt.goal_hyps,
      Typ("?"^to_string int gt.goal_meta.meta_key,
          to_string term gt.goal_type)
  | Unif(c,t,u) ->
      let ctx_elt (v,ty,def) =
        to_string var v,
        match def with
        | None -> to_string term (Eval.snf_beta ty)
        | Some d -> "≔ "^to_string term d
      in
      List.rev_map ctx_elt c,
      Unif(to_string term t^" ≡ "^to_string term u)

(** [add_goals_of_problem p gs] extends the list of goals [gs] with the
   metavariables and constraints of [p]. *)
let add_goals_of_problem : problem -> goal list -> goal list = fun p gs ->
  let gs = MetaSet.fold (fun m gs -> of_meta m :: gs) !p.metas gs in
  let f gs c = Unif c :: gs in
  let gs = List.fold_left f gs !p.to_solve in
  List.fold_left f gs !p.unsolved
