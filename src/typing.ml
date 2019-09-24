(** Type inference and type checking. *)

open Extra
open Timed
open Console
open Terms
open Print
open Unif
open Infer

(** [check builtins ctx t a] tells whether [t] has type [a] in context
   [ctx]. *)
let check : sym StrMap.t -> Ctxt.t -> term -> term -> bool =
  fun builtins ctx t a ->
  if !log_enabled then log_type "check [%a] [%a]" pp t pp a;
  let to_solve = Infer.check ctx t a in
  match solve builtins true {no_problems with to_solve} with
  | None     -> false
  | Some(cs) ->
      let fn (a,b) = log_type (red "Cannot solve [%a] ~ [%a].") pp a pp b in
      if !log_enabled then List.iter fn cs; cs = []

(** [infer_constr builtins ctx t] tries to infer a type [a], together with
   unification constraints [cs], for the term [t] in context [ctx].  The
   function returns [Some(a,cs)] in case of success, and [None] otherwise. *)
let infer_constr
    : sym StrMap.t -> Ctxt.t -> term -> (unif_constrs * term) option =
  fun builtins ctx t ->
  if !log_enabled then log_type "infer_constr [%a]" pp t;
  let (a, to_solve) = Infer.infer ctx t in
  Option.map (fun cs -> (cs, a))
    (solve builtins true {no_problems with to_solve})

(** [infer builtins ctx t] tries to infer a type [a] for [t] in the context
   [ctx]. The function returns [Some(a)] in case of success, and [None]
   otherwise. *)
let infer : sym StrMap.t -> Ctxt.t -> term -> term option =
  fun builtins ctx t ->
  match infer_constr builtins ctx t with
  | None       -> None
  | Some([],a) -> Some(a)
  | Some(cs,_) ->
      let fn (a,b) = log_type (red "Cannot solve [%a] ~ [%a].") pp a pp b in
      if !log_enabled then List.iter fn cs; None

(** [sort_type builtins ctx t] checks that the type of the term [t] in context
   [ctx] is a sort. If that is not the case, the exception [Fatal] is
   raised. *)
let sort_type : sym StrMap.t -> Ctxt.t -> term -> unit =
  fun builtins ctx t ->
  if !log_enabled then log_type "sort_type [%a]" pp t;
  match infer builtins ctx t with
  | None    -> fatal_no_pos "Unable to infer a sort for [%a]." pp t
  | Some(a) ->
  match unfold a with
  | Type | Kind -> ()
  | a           -> fatal_no_pos "[%a] has type [%a] (not a sort)." pp t pp a
