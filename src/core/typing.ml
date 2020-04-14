(** Type inference and type checking. *)

open Extra
open Console
open Terms
open Unif

(** [check builtins ctx t a] tells whether [t] has type [a] in context
   [ctx]. *)
let check : Builtin.map -> ctxt -> term -> term -> bool =
  fun builtins ctx t a ->
  let to_solve = Infer.check ctx t a in
  match solve builtins {empty_problem with to_solve} with
  | None     -> false
  | Some([]) -> true
  | Some(cs) ->
      List.iter (fatal_msg "Cannot solve %a.\n" Print.constr) cs; false

(** [infer_constr builtins ctx t] tries to infer a type [a], together with
   unification constraints [cs], for the term [t] in context [ctx].  The
   function returns [Some(a,cs)] in case of success, and [None] otherwise. *)
let infer_constr
    : Builtin.map -> ctxt -> term -> (term * constr list) option =
  fun builtins ctx t ->
  let (a, to_solve) = Infer.infer ctx t in
  Option.map (fun cs -> (a, cs))
    (solve builtins {empty_problem with to_solve})

(** [infer builtins ctx t] tries to infer a type [a] for [t] in the context
   [ctx]. The function returns [Some(a)] in case of success, and [None]
   otherwise. *)
let infer : Builtin.map -> ctxt -> term -> term option =
  fun builtins ctx t ->
  match infer_constr builtins ctx t with
  | None       -> None
  | Some(a,[]) -> Some(a)
  | Some(_,cs) ->
      List.iter (fatal_msg "Cannot solve %a.\n" Print.constr) cs; None

(** [sort_type builtins ctx t] checks that the type of the term [t] in context
   [ctx] is a sort. If that is not the case, the exception [Fatal] is
   raised. *)
let sort_type : Builtin.map -> ctxt -> term -> unit =
  fun builtins ctx t ->
  match infer builtins ctx t with
  | None    -> fatal None "Unable to infer a sort for %a." Print.term t
  | Some(a) ->
  match unfold a with
  | Type | Kind -> ()
  | a           ->
      fatal None "%a has type %a (not a sort)." Print.term t Print.term a
