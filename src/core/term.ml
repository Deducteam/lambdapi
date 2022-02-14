(** Internal representation of terms.

   This module contains the definition of the internal representation of
   terms, together with smart constructors and low level operation. The
   representation strongly relies on the {!module:Bindlib} library, which
   provides a convenient abstraction to work with binders.

    @see <https://rlepigre.github.io/ocaml-bindlib/> *)

open Timed
open Lplib open Base
open Common open Debug

let log_term = Logger.make 'm' "term" "term building"
let log_term = log_term.pp

(** {3 Term (and symbol) representation} *)

(** Representation of a possibly qualified identifier. *)
type qident = Path.t * string

(** Pattern-matching strategy modifiers. *)
type match_strat =
  | Sequen
  (** Rules are processed sequentially: a rule can be applied only if the
      previous ones (in the order of declaration) cannot be. *)
  | Eager
  (** Any rule that filters a term can be applied (even if a rule defined
      earlier filters the term as well). This is the default. *)

(** Specify the visibility and usability of symbols outside their module. *)
type expo =
  | Public (** Visible and usable everywhere. *)
  | Protec (** Visible everywhere but usable in LHS arguments only. *)
  | Privat (** Not visible and thus not usable. *)

(** Symbol properties. *)
type prop =
  | Defin (** Definable. *)
  | Const (** Constant. *)
  | Injec (** Injective. *)
  | Commu (** Commutative. *)
  | Assoc of bool (** Associative left if [true], right if [false]. *)
  | AC of bool (** Associative and commutative. *)

(** Representation of a term (or types) in a general sense. Values of the type
    are also used, for example, in the representation of patterns or rewriting
    rules. Specific constructors are included for such applications,  and they
    are considered invalid in unrelated code. *)
type term =
  | Vari of tvar (** Free variable. *)
  | Type (** "TYPE" constant. *)
  | Kind (** "KIND" constant. *)
  | Symb of sym (** User-defined symbol. *)
  | Prod of term * tbinder (** Dependent product. *)
  | Abst of term * tbinder (** Abstraction. *)
  | Appl of term * term (** Term application. *)
  | Meta of meta * term array (** Metavariable application. *)
  | Patt of int option * string * term array
  (** Pattern variable application (only used in rewriting rules). *)
  | Db of int (** Bound variable as de Bruijn index. *)
  | Wild
  | Plac of bool
  | TRef of term option ref (** Reference cell (used in surface matching). *)
  | LLet of term * term * tbinder
  (** [LLet(a, t, u)] is [let x : a ≔ t in u] (with [x] bound in [u]). *)

(** {b NOTE} that a wildcard "_" of the concrete (source code) syntax may have
    a different representation depending on the application. For instance, the
    {!constructor:Wild} constructor is only used when matching patterns (e.g.,
    with the "rewrite" tactic). In the LHS of a rewriting {!type:rule}, we use
    the {!constructor:Patt} constructor to represend wildcards of the concrete
    syntax. They are thus considered to be fresh, unused pattern variables. *)

(** Representation of a rewriting rule RHS. *)
and rhs = term

(** Representation of a decision tree (used for rewriting). *)
and dtree = rule Tree_type.dtree

(** Representation of a user-defined symbol. Symbols carry a "mode" indicating
    whether they may be given rewriting rules or a definition. Invariants must
    be enforced for "mode" consistency (see {!type:sym_prop}).  *)
and sym =
  { sym_expo  : expo (** Visibility. *)
  ; sym_path  : Path.t (** Module in which the symbol is defined. *)
  ; sym_name  : string (** Name. *)
  ; sym_type  : term ref (** Type. *)
  ; sym_impl  : bool list (** Implicit arguments ([true] meaning implicit). *)
  ; sym_prop  : prop (** Property. *)
  ; sym_def   : term option ref (** Definition with ≔. *)
  ; sym_opaq  : bool (** Opacity. *)
  ; sym_rules : rule list ref (** Rewriting rules. *)
  ; sym_mstrat: match_strat (** Matching strategy. *)
  ; sym_dtree : dtree ref (** Decision tree used for matching. *)
  ; sym_pos   : Pos.popt (** Position in source file. *) }

(** {b NOTE} {!field:sym_type} holds a (timed) reference for a  technical
    reason related to the writing of signatures as binary files  (in  relation
    to {!val:Sign.link} and {!val:Sign.unlink}).  This is necessary to
    ensure that two identical symbols are always physically equal, even across
    signatures. It should NOT be otherwise mutated. *)

(** {b NOTE} We maintain the invariant that {!field:sym_impl} never ends  with
    [false]. Indeed, this information would be redundant. If a symbol has more
    arguments than there are booleans in the list then the extra arguments are
    all explicit. Finally, note that {!field:sym_impl} is empty if and only if
    the symbol has no implicit parameters. *)

(** {b NOTE} {!field:sym_prop} restricts the possible
    values of {!field:sym_def} and {!field:sym_rules} fields. A symbol is
    not allowed to be given rewriting rules (or a definition) when its mode is
    set to {!constructor:Constant}. Moreover, a symbol should not be given at
    the same time a definition (i.e., {!field:sym_def} different from [None])
    and rewriting rules (i.e., {!field:sym_rules} is non-empty). *)

(** {b NOTE} For generated symbols (recursors, axioms), {!field:sym_pos} may
   not be valid positions in the source. These virtual positions are however
   important for exporting lambdapi files to other formats. *)

(** {3 Representation of rewriting rules} *)

(** Representation of a rewriting rule. A rewriting rule is mainly formed of a
    LHS (left hand side),  which is the pattern that should be matched for the
    rule to apply, and a RHS (right hand side) giving the action to perform if
    the rule applies. More explanations are given below. *)
 and rule =
  { lhs      : term list (** Left hand side (LHS). *)
  ; rhs      : rhs (** Right hand side (RHS). *)
  ; arity    : int (** Required number of arguments to be applicable. *)
  ; arities  : int array
  (** Arities of the pattern variables bound in the RHS. *)
  ; vars_nb  : int (** Number of variables in [lhs]. *)
  ; xvars_nb : int (** Number of variables in [rhs] but not in [lhs]. *)
  ; rule_pos : Pos.popt (** Position of the rule in the source file. *) }

(** {b NOTE} {!field:arity} gives the number of arguments contained in the
   LHS. It is always equal to [List.length r.lhs] and gives the minimal number
   of arguments required to match the LHS. *)

(** {b NOTE} For generated rules, {!field:rule_pos} may not be valid positions
   in the source. These virtual positions are however important for exporting
   lambdapi files to other formats. *)

(** All variables of rewriting rules that appear in the RHS must appear in the
   LHS. This constraint is checked in {!module:Sr}. In the case of unification
   rules, we allow variables to appear only in the RHS. In that case, these
   variables are replaced by fresh meta-variables each time the rule is
   used. *)

(** During evaluation, we only try to apply rewriting rules when we reduce the
   application of a symbol [s] to a list of argument [ts]. At this point, the
   symbol [s] contains every rule [r] that can potentially be applied in its
   {!field:sym_rules} field. To check if a rule [r] applies, we match the
   elements of [r.lhs] with those of [ts] while building an environment [env].
   During this process, a pattern of
   the form {!constructor:Patt}[(Some i,s,e)] matched against a term [u] will
   results in [env.(i)] being set to [u]. If all terms of [ts] can be matched
   against corresponding patterns, then environment [env] is fully constructed
   and it can hence be substituted in [r.rhs] with [Bindlib.msubst r.rhs env]
   to get the result of the application of the rule. *)

(** {3 Metavariables and related functions} *)

(** Representation of a metavariable,  which corresponds to a yet unknown
    term typable in some context. The substitution of the free variables
    of the context is suspended until the metavariable is instantiated
    (i.e., set to a particular term).  When a metavariable [m] is
    instantiated,  the suspended substitution is  unlocked and terms of
    the form {!constructor:Meta}[(m,env)] can be unfolded. *)
 and meta =
  { meta_key   : int (** Unique key. *)
  ; meta_type  : term ref (** Type. *)
  ; meta_arity : int (** Arity (environment size). *)
  ; meta_value : tmbinder option ref (** Definition. *) }

and tbinder = string * term

and tmbinder = string array * term

and tvar = int * string

module Bindlib = struct

(** [unfold t] repeatedly unfolds the definition of the surface constructor
   of [t], until a significant {!type:term} constructor is found.  The term
   that is returned cannot be an instantiated metavariable or term
   environment nor a reference cell ({!constructor:TRef} constructor). Note
   that the returned value is physically equal to [t] if no unfolding was
   performed. {b NOTE} that {!val:unfold} must (almost) always be called
   before matching over a value of type {!type:term}. *)
let rec unfold : term -> term = fun t ->
  match t with
  | Meta(m, ts) ->
      begin
        match !(m.meta_value) with
        | None    -> t
        | Some(b) -> unfold (msubst b ts)
      end
  | TRef(r) ->
      begin
        match !r with
        | None    -> t
        | Some(v) -> unfold v
      end
  | _ -> t

(** Printing functions for debug. *)
and term : term pp = fun ppf t ->
  match unfold t with
  | Db k -> out ppf "`%d" k
  | Vari v -> var ppf v
  | Type -> out ppf "TYPE"
  | Kind -> out ppf "KIND"
  | Symb s -> sym ppf s
  | Prod(a,(n,b)) -> out ppf "(Π %s: %a, %a)" n term a term b
  | Abst(a,(n,b)) -> out ppf "(λ %s: %a, %a)" n term a term b
  | Appl(a,b) -> out ppf "(%a %a)" term a term b
  | Meta(m,ts) -> out ppf "?%d%a" m.meta_key terms ts
  | Patt(i,s,ts) -> out ppf "$%a_%s%a" (D.option D.int) i s terms ts
  | Plac(_) -> out ppf "_"
  | Wild -> out ppf "_"
  | TRef r -> out ppf "&%a" (Option.pp term) !r
  | LLet(a,t,(n,b)) ->
    out ppf "let %s : %a ≔ %a in %a" n term a term t term b
and var : tvar pp = fun ppf (i,n) -> out ppf "%s%d" n i
and sym : sym pp = fun ppf s -> string ppf s.sym_name
and terms : term array pp = fun ppf ts ->
  if Array.length ts > 0 then D.array term ppf ts

(** [lift l t] updates indices when [t] is moved under [l] binders. *)
and lift : int -> term -> term = fun l t ->
  let rec lift i t =
    match unfold t with
    | Db k -> if k < i then t else Db (k+l)
    | Appl(a,b) -> (*FIXME: mk_Appl*) Appl(lift i a, lift i b)
    | Abst(a,(n,u)) -> Abst(lift i a, (n, lift (i+1) u))
    | Prod(a,(n,u)) -> Prod(lift i a, (n ,lift (i+1) u))
    | LLet(a,t,(n,u)) -> LLet(lift i a, lift i t, (n, lift (i+1) u))
    | Meta(m,ts) -> Meta(m, Array.map (lift i) ts)
    | Patt(j,n,ts) -> Patt(j,n, Array.map (lift i) ts)
    | _ -> t
  in
  let r = lift 1 t in
  if Logger.log_enabled() then log_term "lift %d %a = %a" l term t term r;
  r

(** [msubst b vs] substitutes the variables bound by [b] with the values [vs].
   Note that the length of the [vs] array should match the arity of the
   multiple binder [b]. *)
and msubst : tmbinder -> term array -> term = fun (ns,t) vs ->
  let n = Array.length ns in
  assert (Array.length vs = n);
  (* [msubst i t] replaces [Db(i+j)] by [lift (i-1) vs.(n-j-1)]
     for all [0 <= j < n]. *)
  let rec msubst i t =
    if Logger.log_enabled() then
      log_term "msubst %d %a %a" i (D.array term) vs term t;
    match unfold t with
    | Db k -> let j = k-i in
      if j<0 then t else (assert(j<n); lift (i-1) vs.(n-1-j))
    | Appl(a,b) -> (*FIXME: mk_Appl*) Appl(msubst i a, msubst i b)
    | Abst(a,(n,u)) -> Abst(msubst i a, (n, msubst (i+1) u))
    | Prod(a,(n,u)) -> Prod(msubst i a, (n, msubst (i+1) u))
    | LLet(a,t,(n,u)) -> LLet(msubst i a, msubst i t, (n, msubst (i+1) u))
    | Meta(m,ts) -> Meta(m, Array.map (msubst i) ts)
    | Patt(j,n,ts) -> Patt(j,n, Array.map (msubst i) ts)
    | _ -> t
  in
  let r = if n = 0 then t else msubst 1 t in
  if Logger.log_enabled() then
    log_term "msubst %a %a = %a" term t (D.array term) vs term r;
  r

let msubst3 :
  (tmbinder * tmbinder * tmbinder) -> term array -> term * term * term =
  fun (b1, b2, b3) ts -> msubst b1 ts, msubst b2 ts, msubst b3 ts

(** [subst b v] substitutes the variable bound by [b] with the value [v]. *)
let subst : tbinder -> term -> term = fun (_,t) v ->
  let rec subst i t =
    (*if Logger.log_enabled() then
      log_term "subst [%d≔%a] %a" i term v term t;*)
    match unfold t with
    | Db k -> if k = i then lift (i-1) v else t
    | Appl(a,b) -> (*FIXME: mk_Appl*) Appl(subst i a, subst i b)
    | Abst(a,(n,u)) -> Abst(subst i a, (n, subst (i+1) u))
    | Prod(a,(n,u)) -> Prod(subst i a, (n ,subst (i+1) u))
    | LLet(a,t,(n,u)) -> LLet(subst i a, subst i t, (n, subst (i+1) u))
    | Meta(m,ts) -> Meta(m, Array.map (subst i) ts)
    | Patt(j,n,ts) -> Patt(j,n, Array.map (subst i) ts)
    | _ -> t
  in
  let r = subst 1 t in
  if Logger.log_enabled() then
    log_term "subst %a [%a] = %a" term t term v term r;
  r

(** [new_var name] creates a new unique variable of name [name]. *)
let new_var : string -> tvar =
  let open Stdlib in let n = ref 0 in fun name -> incr n; !n, name

(** [name_of x] returns the name of variable [x]. *)
let name_of : tvar -> string = fun (_i,n) -> n (*^ string_of_int i*)

(** [unbind b] substitutes the binder [b] using a fresh variable. The variable
    and the result of the substitution are returned. Note that the name of the
    fresh variable is based on that of the binder. *)
let unbind : tbinder -> tvar * term = fun ((name,_) as b) ->
  let x = new_var name in x, subst b (Vari x)

(** [unbind2 f g] is similar to [unbind f], but it substitutes two binders [f]
    and [g] at once using the same fresh variable. The name of the variable is
    based on that of the binder [f]. *)
let unbind2 : tbinder -> tbinder -> tvar * term * term =
  fun ((name1,_) as b1) b2 ->
  let x = new_var name1 in x, subst b1 (Vari x), subst b2 (Vari x)

(** [unmbind b] substitutes the multiple binder [b] with fresh variables. This
    function is analogous to [unbind] for binders. Note that the names used to
    create the fresh variables are based on those of the multiple binder. *)
let unmbind : tmbinder -> tvar array * term = fun ((names,_) as b) ->
  let xs = Array.init (Array.length names) (fun i -> new_var names.(i)) in
  xs, msubst b (Array.map (fun x -> Vari x) xs)

(** [bind_var x b] binds the variable [x] in [b], producing a boxed binder. *)
let bind_var  : tvar -> term -> tbinder = fun ((_,n) as x) ->
  let rec bind i t =
    (*if Logger.log_enabled() then log_term "bind_var %d %a" i term t;*)
    match unfold t with
    | Vari y when y == x -> Db i
    | Appl(a,b) -> Appl(bind i a, bind i b)
    | Abst(a,(n,u)) -> Abst(bind i a, (n, bind (i+1) u))
    | Prod(a,(n,u)) -> Prod(bind i a, (n, bind (i+1) u))
    | LLet(a,t,(n,u)) -> LLet(bind i a, bind i t, (n, bind (i+1) u))
    | Meta(m,ts) -> Meta(m, Array.map (bind i) ts)
    | Patt(j,n,ts) -> Patt(j,n, Array.map (bind i) ts)
    | _ -> t
  in fun t ->
    let b = bind 1 t in
    if Logger.log_enabled() then
      log_term "bind_var %a %a = %a" var x term t term b;
    n, b

(** [bind_mvar xs b] binds the variables of [xs] in [b] to get a boxed binder.
    It is the equivalent of [bind_var] for multiple variables. *)
let bind_mvar : tvar array -> term -> tmbinder = fun xs t ->
  let n = Array.length xs in
  if n = 0 then [||], t else
  let open Stdlib in let open Extra in
  (*if Logger.log_enabled() then
    log_term "bind_mvar %a" (D.array var) xs;*)
  let map = ref IntMap.empty in
  Array.iteri (fun i (ki,_) -> map := IntMap.add ki (n-1-i) !map) xs;
  let rec bind i t =
    (*if Logger.log_enabled() then log_term "bind_mvar %d %a" i term t;*)
    match unfold t with
    | Vari (key,_) ->
      (match IntMap.find_opt key !map with Some k -> Db (i+k) | None -> t)
    | Appl(a,b) -> Appl(bind i a, bind i b)
    | Abst(a,(n,u)) -> Abst(bind i a, (n, bind (i+1) u))
    | Prod(a,(n,u)) -> Prod(bind i a, (n, bind (i+1) u))
    | LLet(a,t,(n,u)) -> LLet(bind i a, bind i t, (n, bind (i+1) u))
    | Meta(m,ts) -> Meta(m, Array.map (bind i) ts)
    | Patt(j,n,ts) -> Patt(j,n, Array.map (bind i) ts)
    | _ -> t
  in
  let b = bind 1 t in
  if Logger.log_enabled() then
    log_term "bind_mvar %a %a = %a" (D.array var) xs term t term b;
  Array.map name_of xs, b

(** [compare_vars x y] safely compares [x] and [y].  Note that it is unsafe to
    compare variables using [Pervasive.compare]. *)
let compare_vars : tvar -> tvar -> int = fun (i,_) (j,_) -> Stdlib.compare i j

(** [eq_vars x y] safely computes the equality of [x] and [y]. Note that it is
    unsafe to compare variables with the polymorphic equality function. *)
let eq_vars : tvar -> tvar -> bool = fun x y -> compare_vars x y = 0

(** [binder_occur b] tests whether the bound variable occurs in [b]. *)
let binder_occur : tbinder -> bool = fun (_,t) ->
  let rec check i t =
    (*if Logger.log_enabled() then
      log_term "binder_occur %d %a" i term t;*)
    match unfold t with
    | Db k when k = i -> raise Exit
    | Appl(a,b) -> check i a; check i b
    | Abst(a,(_,u))
    | Prod(a,(_,u)) -> check i a; check (i+1) u
    | LLet(a,t,(_,u)) -> check i a; check i t; check (i+1) u
    | Meta(_,ts)
    | Patt(_,_,ts) -> Array.iter (check i) ts
    | _ -> ()
  in
  let r = try check 1 t; false with Exit -> true in
  if Logger.log_enabled() then
    log_term "binder_occur 1 %a = %b" term t r;
  r

(** [binder_constant b] tests whether the [binder] [b] is constant (i.e.,  its
    bound variable does not occur). *)
let binder_constant : tbinder -> bool = fun b -> not (binder_occur b)

(** [mbinder_arity b] gives the arity of the [mbinder]. *)
let mbinder_arity : tmbinder -> int = fun (names,_) -> Array.length names

(** [is_closed t] checks whether [t] is closed. *)
let is_closed : term -> bool =
  let rec check t =
    match unfold t with
    | Vari _ -> raise Exit
    | Appl(a,b) -> check a; check b
    | Abst(a,(_,u))
    | Prod(a,(_,u)) -> check a; check u
    | LLet(a,t,(_,u)) -> check a; check t; check u
    | Meta(_,ts)
    | Patt(_,_,ts) -> Array.iter check ts
    | _ -> ()
  in fun t -> try check t; true with Exit -> false

let is_closed_tmbinder : tmbinder -> bool = fun (_,t) -> is_closed t

(** [occur x t] tells whether variable [x] occurs in [t]. *)
let occur : tvar -> term -> bool = fun x ->
  let rec check t =
    match unfold t with
    | Vari y when y == x -> raise Exit
    | Appl(a,b) -> check a; check b
    | Abst(a,(_,u))
    | Prod(a,(_,u)) -> check a; check u
    | LLet(a,t,(_,u)) -> check a; check t; check u
    | Meta(_,ts)
    | Patt(_,_,ts) -> Array.iter check ts
    | _ -> ()
  in fun t -> try check t; false with Exit -> true

let occur_tmbinder : tvar -> tmbinder -> bool = fun x (_,t) -> occur x t

end

let unfold = Bindlib.unfold

(** Printing functions for debug. *)
module Raw = struct
  let sym = Bindlib.sym
  let term = Bindlib.term
end

(** Minimize [impl] to enforce our invariant (see {!type:Terms.sym}). *)
let minimize_impl : bool list -> bool list =
  let rec rem_false l = match l with false::l -> rem_false l | _ -> l in
  fun l -> List.rev (rem_false (List.rev l))

(** Typing context associating a [Bindlib] variable to a type and possibly a
    definition. The typing environment [x1:A1,..,xn:An] is represented by the
    list [xn:An;..;x1:A1] in reverse order (last added variable comes
    first). *)
type ctxt = (tvar * term * term option) list

(** Typing context with lifted terms. Used to optimise type checking and avoid
    lifting terms several times. Definitions are not included because these
    contexts are used to create meta variables types, which do not use [let]
    definitions. *)
type bctxt = (tvar * term) list

(** Type of unification constraints. *)
type constr = ctxt * term * term

(** Sets and maps of term variables. *)
module Var = struct
  type t = tvar
  let compare = Bindlib.compare_vars
end

module VarSet = Set.Make(Var)
module VarMap = Map.Make(Var)

(** [new_tvar s] creates a new [tvar] of name [s]. *)
let new_tvar : string -> tvar = Bindlib.new_var

(** [new_tvar_ind s i] creates a new [tvar] of name [s ^ string_of_int i]. *)
let new_tvar_ind : string -> int -> tvar = fun s i ->
  new_tvar (Escape.add_prefix s (string_of_int i))

(** Sets and maps of symbols. *)
module Sym = struct
  type t = sym
  let compare s1 s2 =
    if s1 == s2 then 0 else
    match Stdlib.compare s1.sym_name s2.sym_name with
    | 0 -> Stdlib.compare s1.sym_path s2.sym_path
    | n -> n
end

module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)

(** Sets and maps of metavariables. *)
module Meta = struct
  type t = meta
  let compare m1 m2 = m2.meta_key - m1.meta_key
end

module MetaSet = Set.Make(Meta)
module MetaMap = Map.Make(Meta)

(** Representation of unification problems. *)
type problem_aux =
  { to_solve  : constr list
  (** List of unification problems to solve. *)
  ; unsolved  : constr list
  (** List of unification problems that could not be solved. *)
  ; recompute : bool
  (** Indicates whether unsolved problems should be rechecked. *)
  ; metas : MetaSet.t
  (** Set of unsolved metas. *) }

type problem = problem_aux ref

(** Create a new empty problem. *)
let new_problem : unit -> problem = fun () ->
 ref {to_solve  = []; unsolved = []; recompute = false; metas = MetaSet.empty}

(** [create_sym path expo prop opaq name typ impl] creates a new symbol with
   path [path], exposition [expo], property [prop], opacity [opaq], matching
   strategy [mstrat], name [name.elt], type [typ], implicit arguments [impl],
   position [name.pos], no definition and no rules. *)
let create_sym : Path.t -> expo -> prop -> match_strat -> bool ->
  Pos.strloc -> term -> bool list -> sym =
  fun sym_path sym_expo sym_prop sym_mstrat sym_opaq
    { elt = sym_name; pos = sym_pos } typ sym_impl ->
  {sym_path; sym_name; sym_type = ref typ; sym_impl; sym_def = ref None;
   sym_opaq; sym_rules = ref []; sym_dtree = ref Tree_type.empty_dtree;
   sym_mstrat; sym_prop; sym_expo; sym_pos }

(** [is_constant s] tells whether [s] is a constant. *)
let is_constant : sym -> bool = fun s -> s.sym_prop = Const

(** [is_injective s] tells whether [s] is injective, which is in partiular the
   case if [s] is constant. *)
let is_injective : sym -> bool = fun s ->
  match s.sym_prop with Const | Injec -> true | _ -> false

(** [is_private s] tells whether the symbol [s] is private. *)
let is_private : sym -> bool = fun s -> s.sym_expo = Privat

(** [is_modulo s] tells whether the symbol [s] is modulo some equations. *)
let is_modulo : sym -> bool = fun s ->
  match s.sym_prop with Assoc _ | Commu | AC _ -> true | _ -> false

(** [is_abst t] returns [true] iff [t] is of the form [Abst(_)]. *)
let is_abst : term -> bool = fun t ->
  match unfold t with Abst(_) -> true | _ -> false

(** [is_prod t] returns [true] iff [t] is of the form [Prod(_)]. *)
let is_prod : term -> bool = fun t ->
  match unfold t with Prod(_) -> true | _ -> false

(** [is_unset m] returns [true] if [m] is not instantiated. *)
let is_unset : meta -> bool = fun m -> !(m.meta_value) = None

(** [is_symb s t] tests whether [t] is of the form [Symb(s)]. *)
let is_symb : sym -> term -> bool = fun s t ->
  match unfold t with Symb(r) -> r == s | _ -> false

(** Total order on terms. *)
let rec cmp : term cmp = fun t t' ->
    match unfold t, unfold t' with
    | Vari x, Vari x' -> Bindlib.compare_vars x x'
    | Type, Type
    | Kind, Kind
    | Wild, Wild -> 0
    | Symb s, Symb s' -> Sym.compare s s'
    | Prod(t,(_,u)), Prod(t',(_,u'))
    | Abst(t,(_,u)), Abst(t',(_,u')) -> lex cmp cmp (t,u) (t',u')
    | Appl(t,u), Appl(t',u') -> lex cmp cmp (u,t) (u',t')
    | Meta(m,ts), Meta(m',ts') ->
        lex Meta.compare (Array.cmp cmp) (m,ts) (m',ts')
    | Patt(i,s,ts), Patt(i',s',ts') ->
        lex3 Stdlib.compare Stdlib.compare (Array.cmp cmp)
          (i,s,ts) (i',s',ts')
    | Db i, Db j -> Stdlib.compare i j
    | TRef r, TRef r' -> Stdlib.compare r r'
    | LLet(a,t,(_,u)), LLet(a',t',(_,u')) ->
        lex3 cmp cmp cmp (a,t,u) (a',t',u')
    | t, t' -> cmp_tag t t'

(** [get_args t] decomposes the {!type:term} [t] into a pair [(h,args)], where
    [h] is the head term of [t] and [args] is the list of arguments applied to
    [h] in [t]. The returned [h] cannot be an [Appl] node. *)
let get_args : term -> term * term list = fun t ->
  let rec get_args t acc =
    match unfold t with
    | Appl(t,u) -> get_args t (u::acc)
    | t         -> t, acc
  in get_args t []

(** [get_args_len t] is similar to [get_args t] but it also returns the length
    of the list of arguments. *)
let get_args_len : term -> term * term list * int = fun t ->
  let rec get_args_len acc len t =
    match unfold t with
    | Appl(t, u) -> get_args_len (u::acc) (len + 1) t
    | t          -> (t, acc, len)
  in
  get_args_len [] 0 t

(** Construction functions of the private type [term]. They ensure some
   invariants:

- In a commutative function symbol application, the first argument is smaller
   than the second one wrt [cmp].

- In an associative and commutative function symbol application, the
   application is built as a left or right comb depending on the associativity
   of the symbol, and arguments are ordered in increasing order wrt [cmp].

- In [LLet(_,_,b)], [Bindlib.binder_constant b = false] (useless let's are
   erased). *)
let mk_Vari x = Vari x
let mk_Type = Type
let mk_Kind = Kind
let mk_Symb x = Symb x
let mk_Prod (a,b) = Prod (a,b)
let mk_Impl (a,b) = let x = new_tvar "_" in Prod(a, Bindlib.bind_var x b)
let mk_Abst (a,b) = Abst (a,b)
let mk_Meta (m,ts) = (*assert (m.meta_arity = Array.length ts);*) Meta (m,ts)
let mk_Patt (i,s,ts) = Patt (i,s,ts)
let mk_Wild = Wild
let mk_Plac b = Plac b
let mk_TRef x = TRef x

let mk_LLet (a,t,u) =
  if Bindlib.binder_constant u then Bindlib.subst u Kind else LLet (a,t,u)

(* We make the equality of terms modulo commutative and
   associative-commutative symbols syntactic by always ordering arguments in
   increasing order and by putting them in a comb form.

   The term [t1 + t2 + t3] is represented by the left comb [(t1 + t2) + t3] if
   + is left associative and [t1 + (t2 + t3)] if + is right associative. *)

let mk_bin s t1 t2 = Appl(Appl(Symb s, t1), t2)

(** [mk_left_comb s t ts] builds a left comb of applications of [s] from
   [t::ts] so that [mk_left_comb s t1 [t2; t3] = mk_bin s (mk_bin s t1 t2)
   t3]. *)
let mk_left_comb : sym -> term -> term list -> term = fun s ->
  List.fold_left (mk_bin s)

(** [mk_right_comb s ts t] builds a right comb of applications of [s] to
   [ts@[p]] so that [mk_right_comb s [t1; t2] t3 = mk_bin s t1 (mk_bin s t2
   t3)]. *)
let mk_right_comb : sym -> term list -> term -> term = fun s ->
  List.fold_right (mk_bin s)

(** [left_aliens s t] returns the list of the biggest subterms of [t] not
   headed by [s], assuming that [s] is left associative and [t] is in
   canonical form. This is the reverse of [mk_left_comb]. *)
let left_aliens : sym -> term -> term list = fun s ->
  let rec aliens acc = function
    | [] -> acc
    | u::us ->
        let h, ts = get_args u in
        if is_symb s h then
          match ts with
          | t1 :: t2 :: _ -> aliens (t2 :: acc) (t1 :: us)
          | _ -> aliens (u :: acc) us
        else aliens (u :: acc) us
  in fun t -> aliens [] [t]

(** [right_aliens s t] returns the list of the biggest subterms of [t] not
   headed by [s], assuming that [s] is right associative and [t] is in
   canonical form. This is the reverse of [mk_right_comb]. *)
let right_aliens : sym -> term -> term list = fun s ->
  let rec aliens acc = function
    | [] -> acc
    | u::us ->
        let h, ts = get_args u in
        if is_symb s h then
          match ts with
          | t1 :: t2 :: _ -> aliens (t1 :: acc) (t2 :: us)
          | _ -> aliens (u :: acc) us
        else aliens (u :: acc) us
  in fun t -> let r = aliens [] [t] in
  if Logger.log_enabled () then
    log_term "right_aliens %a %a = %a"
      Raw.sym s Raw.term t (D.list Raw.term) r;
  r

(* unit test *)
let _ =
  let s = create_sym [] Privat (AC true) Eager false (Pos.none "+") Kind [] in
  let t1 = Vari (new_tvar "x1") in
  let t2 = Vari (new_tvar "x2") in
  let t3 = Vari (new_tvar "x3") in
  let left = mk_bin s (mk_bin s t1 t2) t3 in
  let right = mk_bin s t1 (mk_bin s t2 t3) in
  let eq = eq_of_cmp cmp in
  assert (eq (mk_left_comb s t1 [t2; t3]) left);
  assert (eq (mk_right_comb s [t1; t2] t3) right);
  let eq = eq_of_cmp (List.cmp cmp) in
  assert (eq (left_aliens s left) [t1; t2; t3]);
  assert (eq (right_aliens s right) [t3; t2; t1])

(** [mk_Appl t u] puts the application of [t] to [u] in canonical form wrt C
   or AC symbols. *)
let mk_Appl : term * term -> term = fun (t, u) ->
  (* if Logger.log_enabled () then
    log_term "mk_Appl(%a, %a)" term t term u;
  let r = *)
  match get_args t with
  | Symb s, [t1] ->
      begin
        match s.sym_prop with
        | Commu when cmp t1 u > 0 -> mk_bin s u t1
        | AC true -> (* left associative symbol *)
            let ts = left_aliens s t1 and us = left_aliens s u in
            begin
              match List.sort cmp (ts @ us) with
              | v::vs -> mk_left_comb s v vs
              | _ -> assert false
            end
        | AC false -> (* right associative symbol *)
            let ts = right_aliens s t1 and us = right_aliens s u in
            let vs, v = List.split_last (List.sort cmp (ts @ us))
            in mk_right_comb s vs v
        | _ -> Appl (t, u)
      end
  | _ -> Appl (t, u)
  (* in
  if Logger.log_enabled () then
    log_term "mk_Appl(%a, %a) = %a" term t term u term r;
  r *)

(** mk_Appl_not_canonical t u] builds the non-canonical (wrt. C and AC
   symbols) application of [t] to [u]. WARNING: to use only in Sign.link. *)
let mk_Appl_not_canonical : term * term -> term = fun (t, u) -> Appl(t, u)

(** [add_args t args] builds the application of the {!type:term} [t] to a list
    arguments [args]. When [args] is empty, the returned value is (physically)
    equal to [t]. *)
let add_args : term -> term list -> term = fun t ts ->
  List.fold_left (fun t u -> mk_Appl(t,u)) t ts

(** [add_args_map f t ts] is equivalent to [add_args t (List.map f ts)] but
   more efficient. *)
let add_args_map : term -> (term -> term) -> term list -> term = fun t f ts ->
  List.fold_left (fun t u -> mk_Appl(t, f u)) t ts

(** Positions in terms in reverse order. The i-th argument of a constructor
   has position i-1. *)
type subterm_pos = int list

let subterm_pos : subterm_pos pp = fun ppf l -> D.(list int) ppf (List.rev l)

(** Type of critical pair positions (pos,l,r,p,l_p). *)
type cp_pos = Pos.popt * term * term * subterm_pos * term

(** Type of a symbol and a rule. *)
type sym_rule = sym * rule

let lhs : sym_rule -> term = fun (s, r) -> add_args (mk_Symb s) r.lhs
let rhs : sym_rule -> term = fun (_, r) -> r.rhs

(** Patt substitution. *)
let subst_patt : tmbinder option array -> term -> term = fun env ->
  let rec subst_patt t =
    match unfold t with
    | Patt(Some i,n,ts) when 0 <= i && i < Array.length env ->
      begin match env.(i) with
        | Some b -> Bindlib.msubst b (Array.map subst_patt ts)
        | None -> mk_Patt(Some i,n,Array.map subst_patt ts)
      end
    | Patt(i,n,ts) -> mk_Patt(i, n, Array.map subst_patt ts)
    | Prod(a,(n,b)) -> mk_Prod(subst_patt a, (n, subst_patt b))
    | Abst(a,(n,b)) -> mk_Abst(subst_patt a, (n, subst_patt b))
    | Appl(a,b) -> mk_Appl(subst_patt a, subst_patt b)
    | Meta(m,ts) -> mk_Meta(m, Array.map subst_patt ts)
    | LLet(a,t,(n,b)) ->
      mk_LLet(subst_patt a, subst_patt t, (n, subst_patt b))
    | Wild
    | Plac _
    | TRef _
    | Db _
    | Vari _
    | Type
    | Kind
    | Symb _ -> t
  in subst_patt

(** [cleanup t] unfold all metas and TRef's in [t]. *)
let rec cleanup : term -> term = fun t ->
  match unfold t with
  | Patt(i,n,ts) -> mk_Patt(i, n, Array.map cleanup ts)
  | Prod(a,(n,b)) -> mk_Prod(cleanup a, (n, cleanup b))
  | Abst(a,(n,b)) -> mk_Abst(cleanup a, (n, cleanup b))
  | Appl(a,b) -> mk_Appl(cleanup a, cleanup b)
  | Meta(m,ts) -> mk_Meta(m, Array.map cleanup ts)
  | LLet(a,t,(n,b)) -> mk_LLet(cleanup a, cleanup t, (n, cleanup b))
  | Wild -> assert false
  | Plac _ -> assert false
  | TRef _ -> assert false
  | Vari _ -> assert false
  | Db _
  | Type
  | Kind
  | Symb _ -> t
