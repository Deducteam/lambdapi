(** Functions to manipulate metavariables. *)

open Term
open Timed

let meta_counter : int Stdlib.ref = Stdlib.ref (-1)

(** [reset_counter ()] resets the counter used to produce meta keys. *)
let reset_meta_counter () = Stdlib.(meta_counter := -1)

(** [fresh p ?name a n] creates a fresh metavariable of type [a] and arity [n]
   with the optional name [name], and adds it to [p]. *)
let fresh : problem -> ?name:string -> term -> int -> meta =
  fun p ?name a n ->
  let m = {meta_key = Stdlib.(incr meta_counter; !meta_counter);
           meta_name = name; meta_type = ref a; meta_arity = n;
           meta_value = ref None } in
  p.metas <- MetaSet.add m p.metas; m

(** [fresh_box p ?name a n] is the boxed counterpart of [fresh_meta]. It is
   only useful in the rare cases where the type of a metavariable contains a
   free term variable environment. This should only happens when scoping the
   rewriting rules, use this function with care.  The metavariable is created
   immediately with a dummy type, and the type becomes valid at unboxing. The
   boxed metavariable should be unboxed at most once, otherwise its type may
   be rendered invalid in some contexts. *)
let fresh_box: problem -> ?name:string -> tbox -> int -> meta Bindlib.box =
  fun p ?name a n ->
  let m = fresh p ?name mk_Kind n in
  Bindlib.box_apply (fun a -> m.meta_type := a; m) a

(** [set p m v] sets the metavariable [m] of [p] to [v]. WARNING: No specific
   check is performed, so this function may lead to cyclic terms. To use with
   care. *)
let set : problem -> meta -> tmbinder -> unit = fun p m v ->
  m.meta_type := mk_Kind; (* to save memory *) m.meta_value := Some v;
  p.metas <- MetaSet.remove m p.metas

(** [name m] returns a string representation of [m]. *)
let name : meta -> string = fun m ->
  match m.meta_name with
  | Some n -> n
  | None -> string_of_int m.meta_key

(** [of_name p n] returns [Some m] if [m] is an element of the set of metas of
   [p] with name [n], and [None] otherwise. *)
let of_name : string -> problem -> meta option = fun n p ->
  let exception Found of meta in
  let f m = if m.meta_name = Some n then raise (Found m) in
  try MetaSet.iter f p.metas; None with Found m -> Some m

(** [make p ctx a] creates a fresh metavariable term of type [a] in the
   context [ctx], and adds it to [p]. *)
let make : problem -> ctxt -> term -> term = fun p ctx a ->
  let a, k = Ctxt.to_prod ctx a in
  let m = fresh p a k in
  let get_var (x,_,_) = mk_Vari x in
  mk_Meta(m, Array.of_list (List.rev_map get_var ctx))

(** [make_codomain p ctx a] creates a fresh metavariable term of type [Type]
   in the context [ctx] extended with a fresh variable of type [a], and
   updates [p] with generated metavariables. *)
let make_codomain : problem -> ctxt -> term -> tbinder = fun p ctx a ->
  let x = new_tvar "x" in
  let b = make p ((x, a, None) :: ctx) mk_Type in
  Bindlib.unbox (Bindlib.bind_var x (lift b))
(* Possible improvement: avoid lift by defining a function _Meta.make
   returning a tbox. *)

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
  (*TODO: make iter tail recursive. *)
  let rec iter t =
    match unfold t with
    | Patt _
    | TEnv _
    | Wild
    | TRef _
    | Type
    | Kind
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
