(** Typing context. *)

open Term
open Lplib
open Timed

(** [type_of x ctx] returns the type of [x] in the context [ctx] when it
    appears in it, and @raise [Not_found] otherwise. *)
let type_of : var -> ctxt -> term = fun x ctx ->
  let (_,a,_) = List.find (fun (y,_,_) -> eq_vars x y) ctx in a

(** [def_of x ctx] returns the definition of [x] in the context [ctx] if it
    appears, and [None] otherwise *)
let rec def_of : var -> ctxt -> ctxt * term option = fun x c ->
  match c with
  | []         -> [], None
  | (y,_,d)::c -> if eq_vars x y then c,d else def_of x c

(** [to_prod ctx t] builds a product by abstracting over the context [ctx], in
    the term [t]. It returns the number of products as well. *)
let to_prod : ctxt -> term -> term * int = fun ctx t ->
  let f (t,k) (x,a,d) =
    let b = bind_var x t in
    let u =
      match d with
      | None -> mk_Prod (a,b)
      | Some d -> mk_LLet (a,d,b)
    in
    u, k+1
  in
  List.fold_left f (t,0) ctx

(** [unfold ctx t] behaves like {!val:Term.unfold} unless term [t] is of the
    form [Vari(x)] with [x] defined in [ctx]. In this case, [t] is replaced by
    the definition of [x] in [ctx].  In particular, if no operation is carried
    out on [t], we have [unfold ctx t == t]. *)
let rec unfold : ctxt -> term -> term = fun ctx t ->
  match t with
  | Meta(m, ts) ->
      begin
        match !(m.meta_value) with
        | None    -> t
        | Some(b) -> unfold ctx (msubst b ts)
      end
  | TRef(r) ->
      begin
        match !r with
        | None    -> t
        | Some(v) -> unfold ctx v
      end
  | Vari(x) ->
      begin
        match def_of x ctx with
        | _, None -> t
        | ctx', Some t -> unfold ctx' t
      end
  | _ -> t

(** [to_map] builds a map from a context. *)
let to_map : ctxt -> term VarMap.t =
  let add_def m (x,_,v) =
    match v with Some v -> VarMap.add x v m | None -> m
  in List.fold_left add_def VarMap.empty
