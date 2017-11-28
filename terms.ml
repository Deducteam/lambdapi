(** Term representation. *)

open Console
open Files

(** Representation of terms (and type). *)
type term =
  (** Free variable. *)
  | Vari of term Bindlib.var
  (** "Type" constant. *)
  | Type
  (** "Kind" constant. *)
  | Kind
  (** Symbol (static or definable). *)
  | Symb of symbol
  (** Dependent product. *)
  | Prod of info * term * (term, term) Bindlib.binder
  (** Abstraction. *)
  | Abst of info * term * (term, term) Bindlib.binder
  (** Application. *)
  | Appl of info * term * term
  (** Unification variable (used for inference). *)
  | Unif of info * unif * term array
  (** Integer tag (used for pattern-matching). *)
  | ITag of int

(** Representation of a (static or definable) symbol. *)
 and symbol = Sym of sym | Def of def

(** Representation of a static symbol. *)
 and sym =
  { sym_name          : string      (** Name of the symbol. *)
  ; mutable sym_type  : term        (** Type of the symbol. *)
  ; sym_path          : module_path (** Module in which it is defined. *) }

(* NOTE the [sym_type] must be mutable so that we can have maximal sharing for
   symbols (two identical symbols are physically equal). We only set the value
   when loading a signature from a file, to link referenced symbols with their
   original definition (in other signatures in memory). Definable symbols also
   need their [def_type] field to be mutable for the same reason. *)

(** Representation of a definable symbol, which carries its reduction rules in
    a reference. It should be updated to add new rules. *)
 and def =
  { def_name          : string      (** Name of the symbol. *)
  ; mutable def_type  : term        (** Type of the symbol. *)
  ; mutable def_rules : rule list   (** Reduction rules for the symbol. *)
  ; def_path          : module_path (** Module in which it is defined. *) }

(** Representation of a reduction rule. The definition of a rule is split into
    a left-hand side [lhs] and a right-and sides [rhs]. The variables that are
    in the context are bound on both sides of the rule. *)
 and rule =
  { lhs   : (term, term list) Bindlib.mbinder (** Left-hand side (pattern). *)
  ; rhs   : (term, term) Bindlib.mbinder      (** Right-hand side. *)
  ; arity : int (** Minimal number of argument for the rule to apply. *) }

(* NOTE the pattern for a rule (or [lhs]) is stored as a list of arguments for
   the definable symbol on which the rule is defined. The symbol itself is not
   given as rules are stored in symbols. *)

(* NOTE to check if rule [r] applies to term [t] using our representation, one
   should first substitute the [r.lhs] binder (using [Bindlib.msubst]) with an
   array of pattern variables [args] (which size should match the arity of the
   binder), thus obtaining a term list [lhs]. Then, to check if [r] applies to
   term [t] (which head must be the definable symbol corresponding to [r]) one
   should test  equality (with unification) between [lhs] and the arguments of
   [t]. If they are not equal then the rule does not match. Otherwise, [t] may
   be rewritten to the term obtained by substituting [r.rhs] with [args] (note
   that its pattern variables should have been substituted at this point. *)

(** Representation of a unification variable (or meta-variable). *)
 and unif =
   { key           : int
   ; mutable value : (term, term) Bindlib.mbinder option }

(* NOTE a unification variables is represented using a multiple binder. Hence,
   it can be instanciated with an open term, which free variables are bound in
   an external environment. Their value is given by the second argument of the
   [Unif] constructor, which can be used to substitute the binder whenever the
   unification variable has been instanciated. *)

(** Additional information on some [term] constructors. *)
 and info =
  { closed : bool (** Set to [true] if the corresponding term is closed. *) }

(** [new_unif ()] creates a fresh unification variable. *)
let new_unif : unit -> unif =
  let c = ref (-1) in
  fun () ->
    incr c;
    if !debug then log "unif" "?%i created" !c;
    { key = !c ; value = None }

(** [unfold t] unfolds the toplevel unification / pattern variables in [t]. *)
let rec unfold : term -> term = fun t ->
  match t with
  | Unif(_, {value = Some(f)}, ar) -> unfold (Bindlib.msubst f ar)
  | _                              -> t

(** Short name for term variables. *)
type tvar = term Bindlib.var

(** Short name for boxed terms. *)
type tbox = term Bindlib.bindbox

(** Injection of [Bindlib] variables into terms. *)
let mkfree : tvar -> term = fun x -> Vari(x)

(** [_Vari x] injects the free variable [x] into the bindbox so that it may be
    available for binding. *)
let _Vari : tvar -> tbox = Bindlib.box_of_var

(** [_Type] injects the constructor [Type] in the [bindbox] type. *)
let _Type : tbox = Bindlib.box Type

(** [_Kind] injects the constructor [Kind] in the [bindbox] type. *)
let _Kind : tbox = Bindlib.box Kind

(** [_Symb s] injects the constructor [Symb(s)] in the [bindbox] type. *)
let _Symb : symbol -> tbox = fun s -> Bindlib.box (Symb(s))

(** [_Appl t u] lifts the application of [t] and [u] to the [bindbox] type. *)
let _Appl : tbox -> tbox -> tbox = fun t u ->
  let closed = Bindlib.is_closed t && Bindlib.is_closed u in
  Bindlib.box_apply2 (fun t u -> Appl({closed},t,u)) t u

(** [_Prod a x f] lifts a dependent product node to the [bindbox] type given a
    boxed term [a] (the type of the domain), a prefered name [x] for the bound
    variable, and a function [f] to build the [binder] (codomain). *)
let _Prod : tbox -> string -> (tvar -> tbox) -> tbox = fun a x f ->
  let b = Bindlib.vbind mkfree x f in
  let closed = Bindlib.is_closed a && Bindlib.is_closed b in
  Bindlib.box_apply2 (fun a b -> Prod({closed},a,b)) a b

(** [_Abst a x f] lifts an abstraction node to the [bindbox] type given a term
    [a] (the type of the bound variable),  the prefered name [x] for the bound
    variable, and the function [f] to build the [binder] (body). *)
let _Abst : tbox -> string -> (tvar -> tbox) -> tbox = fun a x f ->
  let b = Bindlib.vbind mkfree x f in
  let closed = Bindlib.is_closed a && Bindlib.is_closed b in
  Bindlib.box_apply2 (fun a b -> Abst({closed},a,b)) a b

(** [_Unif u ar] lifts a unification variable [u] to the [bindbox] type, given
    its environment [ar]. The unification variable should not  be instanciated
    when calling this function. *)
let _Unif : unif -> tbox array -> tbox = fun u ar ->
  assert(u.value = None);
  let closed = Array.for_all Bindlib.is_closed ar in
  Bindlib.box_apply (fun ar -> Unif({closed},u,ar)) (Bindlib.box_array ar)

let _ITag : int -> tbox = fun i -> Bindlib.box (ITag(i))

(** [lift t] lifts a [term] [t] to the [bindbox] type, thus gathering its free
    variables, making them available for binding. At the same time,  the names
    of the bound variables are automatically updated by [Bindlib]. *)
let rec lift : term -> tbox = fun t ->
  let lift_binder b x = lift (Bindlib.subst b (mkfree x)) in
  let t = unfold t in
  match t with
  | Vari(x)     -> _Vari x
  | Type        -> _Type
  | Kind        -> _Kind
  | Symb(s)     -> _Symb s
  | Prod(i,_,_) when i.closed -> Bindlib.box t
  | Prod(_,a,b) -> _Prod (lift a) (Bindlib.binder_name b) (lift_binder b)
  | Abst(i,_,_) when i.closed -> Bindlib.box t
  | Abst(_,a,t) -> _Abst (lift a) (Bindlib.binder_name t) (lift_binder t)
  | Appl(i,_,_) when i.closed -> Bindlib.box t
  | Appl(_,t,u) -> _Appl (lift t) (lift u)
  | Unif(i,_,_) when i.closed -> Bindlib.box t
  | Unif(_,r,m) -> _Unif r (Array.map lift m)
  | ITag(i)     -> _ITag i

(** [is_closed t] tests whether the term [t] is closed,  using the information
    stored in the [info] elements. *)
let rec is_closed : term -> bool = fun t ->
  match unfold t with
  | Vari(_)     -> false
  | Prod(i,_,_) -> i.closed
  | Abst(i,_,_) -> i.closed
  | Appl(i,_,_) -> i.closed
  | Unif(i,_,m) -> i.closed
  | _           -> true

(** [appl t u] builds the application of the terms [t] and [u] (outside of the
    [bindbox] type), computing the correct value for the [closed] field. *)
let appl : term -> term -> term = fun t u ->
  let closed = is_closed t && is_closed u in
  Appl({closed},t,u)

(** [prod a b] builds the product type of domain [a] and codomain [b] (outside 
    of the [bindbox] type), computing the correct value for [closed]. *)
let prod : term -> (term, term) Bindlib.binder -> term = fun a b ->
  let closed = is_closed a && Bindlib.binder_closed b in
  Prod({closed},a,b) 

(** [get_args t] returns a tuple [(h, args)] where [h] if the head of the term
    and [args] is the list of its arguments. *)
let get_args : term -> term * term list = fun t ->
  let rec get_args acc t =
    match unfold t with
    | Appl(_,t,u) -> get_args (u::acc) t
    | t           -> (t, acc)
  in get_args [] t

(** [add_args h args] builds the application of a term [h] to a list [args] of
    of arguments. This function is the inverse of [get_args]. *)
let add_args : term -> term list -> term = fun t args ->
  let rec add_args t args =
    match args with
    | []      -> t
    | u::args -> add_args (appl t u) args
  in add_args t args

(** [symbol_type s] returns the type of the given symbol [s]. *)
let symbol_type : symbol -> term = fun s ->
  match s with
  | Sym(s) -> s.sym_type
  | Def(d) -> d.def_type
