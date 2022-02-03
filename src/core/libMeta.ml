(** Functions to manipulate metavariables. *)

open Lplib
open Term
open Timed

let meta_counter : int Stdlib.ref = Stdlib.ref (-1)

(** [reset_meta_counter ()] resets the counter used to produce meta keys. *)
let reset_meta_counter () = Stdlib.(meta_counter := -1)

(** [fresh p ?name a n] creates a fresh metavariable of type [a] and arity [n]
   with the optional name [name], and adds it to [p]. *)
let fresh : problem -> term -> int -> meta =
  fun p a n ->
  let m = {meta_key = Stdlib.(incr meta_counter; !meta_counter);
           meta_type = ref a; meta_arity = n;
           meta_value = ref None } in
  p := {!p with metas = MetaSet.add m !p.metas}; m

(** [fresh_box p a n] is the boxed counterpart of [fresh_meta]. It is
    only useful in the rare cases where the type of a metavariable
    contains a free term variable environment. This should only happens
    when scoping the rewriting rules, use this function with care.
    The metavariable is created immediately with a dummy type, and the
    type becomes valid at unboxing. The boxed metavariable should be
    unboxed at most once, otherwise its type may be rendered invalid in
    some contexts. *)
let fresh_box: problem -> tbox -> int -> meta Bindlib.box =
  fun p a n ->
  let m = fresh p mk_Kind n in
  Bindlib.box_apply (fun a -> m.meta_type := a; m) a

(** [set p m v] sets the metavariable [m] of [p] to [v]. WARNING: No specific
   check is performed, so this function may lead to cyclic terms. To use with
   care. *)
let set : problem -> meta -> tmbinder -> unit = fun p m v ->
  m.meta_type := mk_Kind; (* to save memory *) m.meta_value := Some v;
  p := {!p with metas = MetaSet.remove m !p.metas}

(** [make p ctx a] creates a fresh metavariable term named [?name] (if
    provided) of type [a] in the context [ctx], and adds it to [p]. *)
let make : problem -> ctxt -> term -> term =
  fun p ctx a ->
  let a, k = Ctxt.to_prod ctx a in
  let m = fresh p a k in
  let get_var (x,_,d) = if d = None then Some (mk_Vari x) else None in
  mk_Meta(m, Array.of_list (List.filter_rev_map get_var ctx))

(** [bmake p bctx a] is the boxed version of {!make}: it creates
    a fresh {e boxed} metavariable in {e boxed} context [bctx] of {e
    boxed} type [a]. It is the same as [lift (make p c b)] (provided that
    [bctx] is boxed [c] and [a] is boxed [b]), but more efficient. *)
let bmake : problem -> bctxt -> tbox -> tbox =
  fun p bctx a ->
  let (a, k) = Ctxt.to_prod_box bctx a in
  let m = fresh_box p a k in
  let get_var (x, _) = _Vari x in
  _Meta_full m (Array.of_list (List.rev_map get_var bctx))

(** [make_codomain p ctx a] creates a fresh metavariable term of type [Type]
    in the context [ctx] extended with a fresh variable of type [a], and
    updates [p] with generated metavariables. *)
let make_codomain : problem -> ctxt -> term -> tbinder = fun p ctx a ->
  let x = new_tvar "x" in
  bind x lift (make p ((x, a, None) :: ctx) mk_Type)

(** [bmake_codomain p bctx a] is [make_codomain p bctx a] but on boxed
    terms. *)
let bmake_codomain : problem -> bctxt -> tbox -> tbinder Bindlib.box =
  fun p bctx a ->
  let x = new_tvar "x" in
  let b = bmake p ((x, a) :: bctx) _Type in
  Bindlib.bind_var x b

(** [iter b f c t] applies the function [f] to every metavariable of [t] and,
   if [x] is a variable of [t] mapped to [v] in the context [c], then to every
   metavariable of [v], and to the type of every metavariable recursively if
   [b] is true. *)
let iter : bool -> (meta -> unit) -> ctxt -> term -> unit = fun b f c ->
  (* Convert the context into a map. *)
  let vm =
    let f vm (x,_,v) =
      match v with
      | Some v -> VarMap.add x v vm
      | None -> vm
    in
    Stdlib.ref (List.fold_left f VarMap.empty c)
  in
  let rec iter t =
    match unfold t with
    | Patt _
    | TEnv _
    | Wild
    | TRef _
    | Type
    | Kind
    | Plac _
    | Symb _ -> ()
    | Vari x ->
        begin match VarMap.find_opt x Stdlib.(!vm) with
        | Some v -> Stdlib.(vm := VarMap.remove x !vm); iter v
        | None -> ()
        end
    | Prod(a,b)
    | Abst(a,b) -> iter a; iter (Bindlib.subst b mk_Kind)
    | Appl(t,u) -> iter t; iter u
    | Meta(m,ts) -> f m; Array.iter iter ts; if b then iter !(m.meta_type)
    | LLet(a,t,u) -> iter a; iter t; iter (Bindlib.subst u mk_Kind)
  in iter

(** [occurs m c t] tests whether the metavariable [m] occurs in the term [t]
   when variables defined in the context [c] are unfolded. *)
let occurs : meta -> ctxt -> term -> bool =
  let exception Found in fun m c t ->
  let f p = if m == p then raise Found in
  try iter false f c t; false with Found -> true
