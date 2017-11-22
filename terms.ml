open Extra
open Console
open Files

type info =
  { closed : bool }

(* Type of terms (and types). *)
type term =
  (* Free variable. *)
  | Vari of tvar
  (* "Type" constant. *)
  | Type
  (* "Kind" constant. *)
  | Kind
  (* Symbol (static or definable). *)
  | Symb of symbol
  (* Dependent product. *)
  | Prod of info * term * (term, term) Bindlib.binder
  (* Abstraction. *)
  | Abst of info * term * (term, term) Bindlib.binder
  (* Application. *)
  | Appl of info * term * term
  (* Unification variable. *)
  | Unif of unif * term array
  (* Pattern variable. *)
  | PVar of term option ref

 and tvar = term Bindlib.var

 and unif = (term, term) Bindlib.mbinder option ref

(* NOTE: the boolean in the [Appl] constructor is set to true for rigid terms.
   They are marked as such during evaluation for terms having a static  symbol
   at their head (this helps avoiding useless copies). *)

(* Representation of a reduction rule.  The [arity] corresponds to the minimal
   number of arguments that are required for the rule to apply. The definition
   of a rule is split into a left-hand side [lhs] and a right-and sides [rhs].
   The variables of the context are bound on both sides of the rule. Note that
   the left-hand side is given as a list of arguments for the definable symbol
   on which the rule is defined. The symbol is not given in the type of rules,
   as rules will be stored in the definition of symbols. *)
 and rule =
  { lhs   : (term, term list) Bindlib.mbinder
  ; rhs   : (term, term) Bindlib.mbinder
  ; arity : int }

(* NOTE: to check if a rule [r] applies on a term [t] using our representation
   is really easy.  First,  one should substitute the [r.lhs] binder (with the
   [Bindlib.msubst] function) using an array of pattern variables  (which size
   should be [Bindlib.mbinder_arity r.lhs]) to obtain a term list [lhs]. Then,
   to check if [r] applies on a the term [t] (which head should be the symbol)
   one should test equality (with unification) between [lhs] and the arguments
   of [t]. If they are equal then the rule applies and the term obtained after
   the application is computed by substituting [r.rhs] with the same array  of
   pattern variables that was used for [l.rhs] (at this point, all the pattern
   variables should have been instanciated by the equality test). If [lhs] and
   the arguments of [t] are not equal, then the rule does not apply. *)

(**** Symbols (static or definable) *****************************************)

(* Representation of a static symbol. *)
and sym =
  { sym_name  : string
  ; sym_type  : term
  ; sym_path  : string list }

(* Representation of a definable symbol,  which carries its reduction rules in
   a reference. It should be updated to add new rules. *)
and def =
  { def_name  : string
  ; def_type  : term
  ; def_rules : rule list ref
  ; def_path  : string list }

(* NOTE: the [path] that is stored in a symbol corresponds to a "module path".
   The path [["a"; "b"; "f"]] corresponds to file ["a/b/f.lp"].  It is printed
   and read in the source code as ["dira::dirb::file"]. *)

(* Representation of a (static or definable) symbol. *)
and symbol = Sym of sym | Def of def

(* [symbol_type s] returns the type of the given symbol [s]. *)
let symbol_type : symbol -> term =
  fun s ->
    match s with
    | Sym(sym) -> sym.sym_type
    | Def(def) -> def.def_type

(* [add_rule def r] adds the new rule [r] to the definable symbol [def]. *)
let add_rule : def -> rule -> unit = fun def r ->
  def.def_rules := !(def.def_rules) @ [r]

(* Short name for boxed terms. *)
type tbox = term Bindlib.bindbox

(* Injection of [Bindlib] variables into terms. *)
let mkfree : tvar -> term = fun x -> Vari(x)

(* [_Vari x] injects the free variable [x] into the bindbox, so that it may be
   available for binding. *)
let _Vari : tvar -> tbox = Bindlib.box_of_var

(* [_Type] injects the constructor [Type] in the [bindbox] type. *)
let _Type : tbox = Bindlib.box Type

(* [_Kind] injects the constructor [Kind] in the [bindbox] type. *)
let _Kind : tbox = Bindlib.box Kind

(* [_Symb s] injects the constructor [Symb(s)] in the [bindbox] type. *)
let _Symb : symbol -> tbox = fun s -> Bindlib.box (Symb(s))

(* [_Appl t u] lifts the application of [t] and [u] to the [bindbox] type. *)
let _Appl : tbox -> tbox -> tbox = fun t u ->
  let closed = Bindlib.is_closed t && Bindlib.is_closed u in
  Bindlib.box_apply2 (fun t u -> Appl({closed},t,u)) t u

(* [_Prod a x f] lifts a dependent product node to the [bindbox] type, given a
   boxed term [a] (the type of the domain),  a prefered name [x] for the bound
   variable, and function [f] to build the [binder] (codomain). *)
let _Prod : tbox -> string -> (tvar -> tbox) -> tbox = fun a x f ->
  let b = Bindlib.vbind mkfree x f in
  let closed = Bindlib.is_closed a && Bindlib.is_closed b in
  Bindlib.box_apply2 (fun a b -> Prod({closed},a,b)) a b

(* [_Abst a x f] lifts an abstraction node to the [bindbox] type, given a term
   [a] (which is the type of the bound variable),  the prefered name [x] to be
   used for the bound variable, and the function [f] to build the [binder]. *)
let _Abst : tbox -> string -> (tvar -> tbox) -> tbox = fun a x f ->
  let b = Bindlib.vbind mkfree x f in
  let closed = Bindlib.is_closed a && Bindlib.is_closed b in
  Bindlib.box_apply2 (fun a b -> Abst({closed},a,b)) a b

let _Unif : unif -> tbox array -> tbox =
  let dummy = Bindlib.box_of_var (Bindlib.new_var mkfree "__dummy__") in
  fun r ar ->
    let ar = Bindlib.box_array ar in
    Bindlib.box_apply2 (fun ar _ -> Unif(r,ar)) ar dummy

(* [unfold t] unfolds the toplevel unification / pattern variables in [t]. *)
let rec unfold : term -> term = fun t ->
  match t with
  | Unif({contents = Some(f)}, e) -> unfold (Bindlib.msubst f e)
  | PVar({contents = Some(t)})    -> unfold t
  | _                             -> t

(* [lift t] lifts a [term] [t] to the [bindbox] type,  thus gathering its free
   variables, making them available for binding.  At the same time,  the names
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
  | Prod(i,a,b) -> _Prod (lift a) (Bindlib.binder_name b) (lift_binder b)
  | Abst(i,_,_) when i.closed -> Bindlib.box t
  | Abst(i,a,t) -> _Abst (lift a) (Bindlib.binder_name t) (lift_binder t)
  | Appl(i,_,_) when i.closed -> Bindlib.box t
  | Appl(_,t,u) -> _Appl (lift t) (lift u)
  | Unif(r,m)   -> _Unif r (Array.map lift m) (* Not instanciated *)
  | PVar(_)     -> Bindlib.box t (* Not instanciated *)

(* [update_names t] updates the names of the bound variables of [t] to prevent
   "visual capture" while printing. Note that with [Bindlib],  real capture is
   not possible as binders are represented as OCaml function (HOAS). *)
let update_names : term -> term = fun t -> Bindlib.unbox (lift t)

(* [get_args t] returns a tuple [(hd,args)] where [hd] if the head of the term
   and [args] its arguments. *)
let get_args : term -> term * term list = fun t ->
  let rec get acc t =
    match unfold t with
    | Appl(_,t,u) -> get (u::acc) t
    | t           -> (t, acc)
  in get [] t

let rec is_closed : term -> bool = fun t ->
  match unfold t with
  | Vari(_)     -> false
  | Prod(i,_,_) -> i.closed
  | Abst(i,_,_) -> i.closed
  | Appl(i,_,_) -> i.closed
  | Unif(_,m)   -> Array.for_all is_closed m
  | PVar(_)     -> assert false
  | _           -> true

let appl : term -> term -> term = fun t u ->
  let closed = is_closed t && is_closed u in
  Appl({closed},t,u)

let prod : term -> (term, term) Bindlib.binder -> term = fun a b ->
  let closed = is_closed a && Bindlib.binder_closed b in
  Prod({closed},a,b) 

(* [add_args hd args] builds the application of a term [hd] to the list of its
   arguments [args] (this is the inverse of [get_args]). *)
let add_args : term -> term list -> term = fun t args ->
  let rec add_args t args =
    match args with
    | []      -> t
    | u::args -> add_args (appl t u) args
  in add_args t args
