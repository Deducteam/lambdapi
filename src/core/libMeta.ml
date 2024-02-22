(** Functions to manipulate metavariables. *)

open Lplib
open Term
open Timed
open Common

(** Logging function for unification. *)
let log = Logger.make 'a' "meta" "metavariables"
let log = log.pp

let meta_counter : int Stdlib.ref = Stdlib.ref (-1)

(** [reset_meta_counter ()] resets the counter used to produce meta keys. *)
let reset_meta_counter () = Stdlib.(meta_counter := -1)

(** [fresh p ?name a n] creates a fresh metavariable of type [a] and arity [n]
   with the optional name [name], and adds it to [p]. *)
let fresh : problem -> term -> int -> meta = fun p a n ->
  let m = {meta_key = Stdlib.(incr meta_counter; !meta_counter);
           meta_type = ref a; meta_arity = n; meta_value = ref None } in
  if Logger.log_enabled() then log "fresh ?%d" m.meta_key;
  p := {!p with metas = MetaSet.add m !p.metas};
  if Logger.log_enabled() then log "%a" Print.problem p;
  m

(** [set p m v] sets the metavariable [m] of [p] to [v]. WARNING: No specific
   check is performed, so this function may lead to cyclic terms. To use with
   care. *)
let set : problem -> meta -> mbinder -> unit = fun p m v ->
  m.meta_type := mk_Kind; (* to save memory *) m.meta_value := Some v;
  p := {!p with metas = MetaSet.remove m !p.metas}

(** [make p ctx a] creates a fresh metavariable term of type [a] in the
   context [ctx], and adds it to [p]. *)
let make : problem -> ctxt -> term -> term = fun p ctx a ->
  let a, k = Ctxt.to_prod ctx a in
  let m = fresh p a k in
  let get_var (x,_,d) = if d = None then Some (mk_Vari x) else None in
  mk_Meta(m, Array.of_list (List.filter_rev_map get_var ctx))

(** [make_codomain p ctx a] creates a fresh metavariable term of type [Type]
    in the context [ctx] extended with a fresh variable of type [a], and
    updates [p] with generated metavariables. *)
let make_codomain : problem -> ctxt -> term -> binder = fun p ctx a ->
  let x = new_var "x" in
  bind_var x (make p ((x, a, None) :: ctx) mk_Type)

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
    | Db _ -> assert false
    | Patt _
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
    | Abst(a,b) -> iter a; iter (subst b mk_Kind)
    | Appl(t,u) -> iter t; iter u
    | Meta(m,ts) -> f m; Array.iter iter ts; if b then iter !(m.meta_type)
    | LLet(a,t,u) -> iter a; iter t; iter (subst u mk_Kind)
  in iter

(** [occurs m c t] tests whether the metavariable [m] occurs in the term [t]
   when variables defined in the context [c] are unfolded. *)
let occurs : meta -> ctxt -> term -> bool =
  let exception Found in fun m c t ->
  let f p = if m == p then raise Found in
  try iter false f c t; false with Found -> true
