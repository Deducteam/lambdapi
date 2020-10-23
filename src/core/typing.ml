(** Type inference and type checking. *)

open! Lplib

open Console
open Terms
open Unif
open Print

(** [check ctx t a] tells whether [t] has type [a] in context [ctx]. *)
let check : ctxt -> term -> term -> bool = fun ctx t a ->
  let to_solve = Infer.check ctx t a in
  match solve {empty_problem with to_solve} with
  | None     -> false
  | Some([]) -> true
  | Some(cs) ->
      List.iter (fatal_msg "Cannot solve %a.\n" pp_constr) cs; false

(** [infer_constr ctx t] tries to infer a type [a], together with
   unification constraints [cs], for the term [t] in context [ctx].  The
   function returns [Some(a,cs)] in case of success, and [None] otherwise. *)
let infer_constr : ctxt -> term -> (term * constr list) option =
  fun ctx t ->
  let (a, to_solve) = Infer.infer ctx t in
  Option.map (fun cs -> (a, cs)) (solve {empty_problem with to_solve})

(** [infer ctx t] tries to infer a type [a] for [t] in the context
   [ctx]. The function returns [Some(a)] in case of success, and [None]
   otherwise. *)
let infer : ctxt -> term -> term option = fun ctx t ->
  match infer_constr ctx t with
  | None       -> None
  | Some(a,[]) -> Some(a)
  | Some(_,cs) ->
      List.iter (fatal_msg "Cannot solve %a.\n" pp_constr) cs; None

(** [sort_type ctx t] checks that the type of the term [t] in context
   [ctx] is a sort. If that is not the case, the exception [Fatal] is
   raised. *)
let sort_type : ctxt -> term -> unit = fun ctx t ->
  match infer ctx t with
  | None    -> fatal None "Unable to infer a sort for %a." pp_term t
  | Some(a) ->
  match unfold a with
  | Type | Kind -> ()
  | a           ->
      fatal None "%a has type %a (not a sort)." pp_term t pp_term a
