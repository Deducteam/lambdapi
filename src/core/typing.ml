(** Type inference and type checking. *)

open Extra
open Console
open Terms
open Unif

(** [check ss ctx t a] tells whether [t] has type [a] in context
   [ctx]. *)
let check : Sig_state.t -> ctxt -> term -> term -> bool =
  fun ss ctx t a ->
  let to_solve = Infer.check ss ctx t a in
  match solve ss {empty_problem with to_solve} with
  | None     -> false
  | Some([]) -> true
  | Some(cs) ->
      let pp_constr = Print.pp_constr ss in
      List.iter (fatal_msg "Cannot solve %a.\n" pp_constr) cs; false

(** [infer_constr ss ctx t] tries to infer a type [a], together with
   unification constraints [cs], for the term [t] in context [ctx].  The
   function returns [Some(a,cs)] in case of success, and [None] otherwise. *)
let infer_constr
    : Sig_state.t -> ctxt -> term -> (term * constr list) option =
  fun ss ctx t ->
  let (a, to_solve) = Infer.infer ss ctx t in
  Option.map (fun cs -> (a, cs)) (solve ss {empty_problem with to_solve})

(** [infer ss ctx t] tries to infer a type [a] for [t] in the context
   [ctx]. The function returns [Some(a)] in case of success, and [None]
   otherwise. *)
let infer : Sig_state.t -> ctxt -> term -> term option =
  fun ss ctx t ->
  match infer_constr ss ctx t with
  | None       -> None
  | Some(a,[]) -> Some(a)
  | Some(_,cs) ->
      let pp_constr = Print.pp_constr ss in
      List.iter (fatal_msg "Cannot solve %a.\n" pp_constr) cs; None

(** [sort_type ss ctx t] checks that the type of the term [t] in context
   [ctx] is a sort. If that is not the case, the exception [Fatal] is
   raised. *)
let sort_type : Sig_state.t -> ctxt -> term -> unit =
  fun ss ctx t ->
  let pp_term = Print.pp_term ss in
  match infer ss ctx t with
  | None    -> fatal None "Unable to infer a sort for %a." pp_term t
  | Some(a) ->
  match unfold a with
  | Type | Kind -> ()
  | a           ->
      fatal None "%a has type %a (not a sort)." pp_term t pp_term a
