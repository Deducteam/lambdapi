(** Type inference and type checking. *)

open Extra
open Console
open Terms
open Print
open Unif

(** [check builtins ctx t a] tells whether [t] has type [a] in context
   [ctx]. *)
let check : sym StrMap.t -> ctxt -> term -> term -> bool =
  fun builtins ctx t a ->
  let to_solve = Infer.check ctx t a in
  match solve builtins true {no_problems with to_solve} with
  | None     -> false
  | Some([]) -> true
  | Some(cs) ->
      let fn (c,a,b) =
        fatal_msg "Cannot solve %a.\n" pp_constr (c, a, b)
      in
      List.iter fn cs; false

(** [infer_constr builtins ctx t] tries to infer a type [a], together with
   unification constraints [cs], for the term [t] in context [ctx].  The
   function returns [Some(a,cs)] in case of success, and [None] otherwise. *)
let infer_constr
    : sym StrMap.t -> ctxt -> term -> (term * unif_constrs) option =
  fun builtins ctx t ->
  let (a, to_solve) = Infer.infer ctx t in
  Option.map (fun cs -> (a, cs))
    (solve builtins true {no_problems with to_solve})

(** [infer builtins ctx t] tries to infer a type [a] for [t] in the context
   [ctx]. The function returns [Some(a)] in case of success, and [None]
   otherwise. *)
let infer : sym StrMap.t -> ctxt -> term -> term option =
  fun builtins ctx t ->
  match infer_constr builtins ctx t with
  | None       -> None
  | Some(a,[]) -> Some(a)
  | Some(_,cs) ->
      let fn (c,a,b) =
        fatal_msg "Cannot solve %a.\n" pp_constr (c, a, b)
      in
      List.iter fn cs; None

(** [sort_type builtins ctx t] checks that the type of the term [t] in context
   [ctx] is a sort. If that is not the case, the exception [Fatal] is
   raised. *)
let sort_type : sym StrMap.t -> ctxt -> term -> unit =
  fun builtins ctx t ->
  match infer builtins ctx t with
  | None    -> fatal None "Unable to infer a sort for [%a]." pp t
  | Some(a) ->
  match unfold a with
  | Type | Kind -> ()
  | a           -> fatal None "[%a] has type [%a] (not a sort)." pp t pp a
