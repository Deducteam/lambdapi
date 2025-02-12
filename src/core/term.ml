(** Internal representation of terms.

   This module contains the definition of the internal representation of
   terms, together with smart constructors and low level operation. *)

open Timed
open Lplib open Base open Extra
open Common open Debug

let log = Logger.make 'm' "term" "term building"
let log = log.pp

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

(** Data of a binder. *)
type binder_info = {binder_name : string; binder_bound : bool}
type mbinder_info = {mbinder_name : string array; mbinder_bound : bool array}

let binder_name : binder_info -> string = fun bi -> bi.binder_name
let pr_bound = D.array (fun ppf b -> if b then out ppf "*" else out ppf "_")

(** Type for free variables. *)
type var = int * string

(** [compare_vars x y] safely compares [x] and [y]. Note that it is unsafe to
    compare variables using [Pervasive.compare]. *)
let compare_vars : var -> var -> int = fun (i,_) (j,_) -> Stdlib.compare i j

(** [eq_vars x y] safely computes the equality of [x] and [y]. Note that it is
    unsafe to compare variables with the polymorphic equality function. *)
let eq_vars : var -> var -> bool = fun x y -> compare_vars x y = 0

(** [new_var name] creates a new unique variable of name [name]. *)
let new_var : string -> var =
  let open Stdlib in let n = ref 0 in fun name -> incr n; !n, name

(** [new_var_ind s i] creates a new [var] of name [s ^ string_of_int i]. *)
let new_var_ind : string -> int -> var = fun s i ->
  new_var (Escape.add_prefix s (string_of_int i))

(** [base_name x] returns the base name of variable [x]. Note that this name
    is not unique: two distinct variables may have the same name. *)
let base_name : var -> string = fun (_i,n) -> n

(** [uniq_name x] returns a string uniquely identifying the variable [x]. *)
let uniq_name : var -> string = fun (i,_) -> "v" ^ string_of_int i

(** Sets and maps of variables. *)
module Var = struct
  type t = var
  let compare = compare_vars
end

module VarSet = Set.Make(Var)
module VarMap = Map.Make(Var)

(** Representation of a term (or types) in a general sense. Values of the type
    are also used, for example, in the representation of patterns or rewriting
    rules. Specific constructors are included for such applications,  and they
    are considered invalid in unrelated code. *)
type term =
  | Vari of var (** Free variable. *)
  | Type (** "TYPE" constant. *)
  | Kind (** "KIND" constant. *)
  | Symb of sym (** User-defined symbol. *)
  | Prod of term * binder (** Dependent product. *)
  | Abst of term * binder (** Abstraction. *)
  | Appl of term * term (** Term application. *)
  | Meta of meta * term array (** Metavariable application. *)
  | Patt of int option * string * term array
  (** Pattern variable application (only used in rewriting rules). *)
  | Db of int (** Bound variable as de Bruijn index (starting at 1). *)
  | Wild (** Wildcard (only used for surface matching, never in LHS). *)
  | Plac of bool
  (** [Plac b] is a placeholder, or hole, for not given terms. Boolean [b] is
      true if the placeholder stands for a type. *)
  | TRef of term option ref (** Reference cell (used in surface matching). *)
  | LLet of term * term * binder
  (** [LLet(a, t, u)] is [let x : a ≔ t in u] (with [x] bound in [u]). *)

(** Type for binders, implemented as closures. The closure term must have
    all its de Bruijn indices bound either by the binder itself or by 
    the closure environment.

    In a binder [(bi,u,e)] of arity [n], dB [i] in [1..n] of [u]
    refers to the bound variable at position [i-1] in the binder array,
    and dB [i] of [u] with [i>n] refers to [e.(n+|e|-i)] *)
and binder = binder_info * term * term list
and mbinder = mbinder_info * term * term list

(** {b NOTE} that a wildcard "_" of the concrete (source code) syntax may have
    a different representation depending on the context. For instance, the
    {!constructor:Wild} constructor is only used when matching patterns (e.g.,
    with the "rewrite" tactic). In the LHS of a rewriting {!type:rule}, we use
    the {!constructor:Patt} constructor to represend wildcards of the concrete
    syntax. They are thus considered to be fresh, unused pattern variables. *)

(** Representation of a decision tree (used for rewriting). *)
and dtree = rule Tree_type.dtree

(** Representation of a user-defined symbol. *)
and sym =
  { sym_expo  : expo (** Visibility. *)
  ; sym_path  : Path.t (** Module in which the symbol is defined. *)
  ; sym_name  : string (** Name. *)
  ; sym_type  : term ref (** Type. *)
  ; sym_impl  : bool list (** Implicit arguments ([true] meaning implicit). *)
  ; sym_prop  : prop (** Property. *)
  ; sym_def   : term option ref (** Definition with ≔. *)
  ; sym_opaq  : bool ref (** Opacity. *)
  ; sym_rules : rule list ref (** Rewriting rules. *)
  ; sym_mstrat: match_strat (** Matching strategy. *)
  ; sym_dtree : dtree ref (** Decision tree used for matching. *)
  ; sym_pos   : Pos.popt (** Position in source file of symbol name. *)
  ; sym_decl_pos : Pos.popt (** Position in source file of symbol declaration
                                without its definition. *) }

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
  ; rhs      : term (** Right hand side (RHS). *)
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
   LHS. In the case of unification rules, we allow variables to appear only in
   the RHS. In that case, these variables are replaced by fresh meta-variables
   each time the rule is used. *)

(** During evaluation, we only try to apply rewriting rules when we reduce the
   application of a symbol [s] to a list of argument [ts]. At this point, the
   symbol [s] contains every rule [r] that can potentially be applied in its
   {!field:sym_rules} field. To check if a rule [r] applies, we match the
   elements of [r.lhs] with those of [ts] while building an environment [env].
   During this process, a pattern of
   the form {!constructor:Patt}[(Some i,_,_)] matched against a term [u] will
   results in [env.(i)] being set to [u]. If all terms of [ts] can be matched
   against corresponding patterns, then environment [env] is fully constructed
   and it can hence be substituted in [r.rhs] with [subst_patt env r.rhs]
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
  ; meta_value : mbinder option ref (** Definition. *) }

(** [mbinder_arity b] gives the arity of the [mbinder]. *)
let mbinder_arity : mbinder -> int = fun (i,_,_) -> Array.length i.mbinder_name

(** Minimize [impl] to enforce our invariant (see {!type:Terms.sym}). *)
let minimize_impl : bool list -> bool list =
  let rec rem_false l = match l with false::l -> rem_false l | _ -> l in
  fun l -> List.rev (rem_false (List.rev l))

(** [create_sym path expo prop mstrat opaq name pos typ impl] creates a new
    symbol with path [path], exposition [expo], property [prop], opacity
    [opaq], matching strategy [mstrat], name [name.elt], type [typ], implicit
    arguments [impl], position [name.pos], declaration position [pos], no
    definition and no rules. *)
let create_sym : Path.t -> expo -> prop -> match_strat -> bool ->
  Pos.strloc -> Pos.popt -> term -> bool list -> sym =
  fun sym_path sym_expo sym_prop sym_mstrat sym_opaq
    { elt = sym_name; pos = sym_pos } sym_decl_pos typ sym_impl ->
  {sym_path; sym_name; sym_type = ref typ; sym_impl; sym_def = ref None;
   sym_opaq = ref sym_opaq; sym_rules = ref [];
   sym_dtree = ref Tree_type.empty_dtree;
   sym_mstrat; sym_prop; sym_expo; sym_pos ; sym_decl_pos }

(** [is_constant s] tells whether [s] is a constant. *)
let is_constant : sym -> bool = fun s -> s.sym_prop = Const

(** [is_injective s] tells whether [s] is injective, which is in partiular the
   case if [s] is constant. *)
let is_injective : sym -> bool = fun s ->
  match s.sym_prop with Const | Injec -> true | _ -> !(s.sym_opaq)

(** [is_private s] tells whether the symbol [s] is private. *)
let is_private : sym -> bool = fun s -> s.sym_expo = Privat

(** [is_modulo s] tells whether the symbol [s] is modulo some equations. *)
let is_modulo : sym -> bool = fun s ->
  match s.sym_prop with Assoc _ | Commu | AC _ -> true | _ -> false

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

(** [is_unset m] returns [true] if [m] is not instantiated. *)
let is_unset : meta -> bool = fun m -> !(m.meta_value) = None

(** Sets and maps of metavariables. *)
module Meta = struct
  type t = meta
  let compare m1 m2 = m2.meta_key - m1.meta_key
end

module MetaSet = Set.Make(Meta)
module MetaMap = Map.Make(Meta)

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

(** Printing functions for debug. *)
let rec term : term pp = fun ppf t ->
  match unfold t with
  | Db k -> out ppf "`%d" k
  | Vari v -> var ppf v
  | Type -> out ppf "TYPE"
  | Kind -> out ppf "KIND"
  | Symb s -> sym ppf s
  | Prod(a,(n,b,e)) -> out ppf "(Π %s: %a, %a)#[%a]" n.binder_name term a term b terms (Array.of_list e)
  | Abst(a,(n,b,e)) -> out ppf "(λ %s: %a, %a)#[%a]" n.binder_name term a term b terms (Array.of_list e)
  | Appl(a,b) -> out ppf "(%a %a)" term a term b
  | Meta(m,ts) -> out ppf "?%d%a" m.meta_key terms ts
  | Patt(i,s,ts) -> out ppf "$%a_%s%a" (D.option D.int) i s terms ts
  | Plac(_) -> out ppf "_"
  | Wild -> out ppf "_"
  | TRef r -> out ppf "&%a" (Option.pp term) !r
  | LLet(a,t,(n,b,e)) ->
    out ppf "let %s : %a ≔ %a in (%a)@[%a]" n.binder_name term a term t term b terms (Array.of_list e)
and var : var pp = fun ppf (i,n) -> out ppf "%s%d" n i
and sym : sym pp = fun ppf s -> string ppf s.sym_name
and terms : term array pp = fun ppf ts ->
  if Array.length ts > 0 then D.array term ppf ts

(** [unfold t] repeatedly unfolds the definition of the surface constructor
   of [t], until a significant {!type:term} constructor is found.  The term
   that is returned can be neither an instantiated metavariable
   nor a reference cell ({!constructor:TRef} constructor). Note
   that the returned value is physically equal to [t] if no unfolding was
   performed. {b NOTE} that {!val:unfold} must (almost) always be called
   before matching over a value of type {!type:term}. *)
and unfold : term -> term = fun t ->
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

(** [msubst b vs] substitutes the variables bound by [b] with the values
    [vs].  Note that the length of the [vs] array should match the arity of
    the multiple binder [b]. *)
and msubst : mbinder -> term array -> term = fun (bi,tm,e) vs ->
  let n = Array.length bi.mbinder_name in
  assert (Array.length vs = n);
  let env = Array.of_list e in
  let m = n+Array.length env in
  (*assert (_db_closed ~bv:bi.mbinder_bound (n+Array.length env) tm);*)
  (* [msubst t] replaces
     [Db(j)] by [vs.(n-j)]  for all [1 <= j <= n] (current substitution)
     and [Db(j)] by [e.(m-j)] for all [n < j <= m] (propagation of previous
     substituttions). *)
  let rec msubst t =
    if Logger.log_enabled() then
      log "msubst %a %a" (D.array term) vs term t;
    match unfold t with
    | Db k -> assert(k<=m);
              if k <= n then (assert (bi.mbinder_bound.(k-1)); vs.(k-1))
              else env.(m-k)
    | Appl(a,b) -> mk_Appl(msubst a, msubst b)
    | Abst(a,(n,u,e)) -> Abst(msubst a, (n, u, List.map msubst e))
    | Prod(a,(n,u,e)) -> Prod(msubst a, (n, u, List.map msubst e))
    | LLet(a,t,(n,u,e)) -> LLet(msubst a, msubst t, (n, u, List.map msubst e))
    | Meta(m,ts) -> Meta(m, Array.map msubst ts)
    | Patt(j,n,ts) -> Patt(j,n, Array.map msubst ts)
    | Type | Kind | Vari _ | Wild | Symb _ | Plac _ | TRef _ -> t
  in
  let r =
    (* TODO: generalizes to case where env is the identity *)
    if Array.for_all ((=) false) bi.mbinder_bound && Array.length env = 0
    then tm
    else msubst tm in
  if Logger.log_enabled() then
    log "msubst %a[%a] %a = %a" term tm terms env (D.array term) vs term r;
  r
  
(** Total order on terms. *)
and cmp : term cmp = fun t t' ->
  match unfold t, unfold t' with
  | Vari x, Vari x' -> compare_vars x x'
  | Type, Type
  | Kind, Kind
  | Wild, Wild -> 0
  | Symb s, Symb s' -> Sym.compare s s'
  | Prod(t,u), Prod(t',u')
  | Abst(t,u), Abst(t',u') -> lex cmp cmp_binder (t,u) (t',u')
  | Appl(t,u), Appl(t',u') -> lex cmp cmp (u,t) (u',t')
  | Meta(m,ts), Meta(m',ts') ->
    lex Meta.compare (Array.cmp cmp) (m,ts) (m',ts')
  | Patt(i,s,ts), Patt(i',s',ts') ->
    lex3 Stdlib.compare Stdlib.compare (Array.cmp cmp)
      (i,s,ts) (i',s',ts')
  | Db i, Db j -> Stdlib.compare i j
  | TRef r, TRef r' -> Stdlib.compare r r'
  | LLet(a,t,u), LLet(a',t',u') ->
    lex3 cmp cmp cmp_binder (a,t,u) (a',t',u')
  | t, t' -> cmp_tag t t'

and cmp_binder : binder cmp =
(*  fun ({binder_name;binder_bound},u,e) (bi',u',e') ->
  let mbi = {mbinder_name=[|binder_name|];mbinder_bound=[|binder_bound|]} in
  let var = Vari(new_var binder_name) in
  cmp (msubst (mbi,u,e)[|var|]) (msubst({mbi with mbinder_bound=[|bi'.binder_bound|]},u',e')[|var|])*)
  fun (_,u,e) (_,u',e') -> lex cmp (List.cmp cmp) (u,e) (u',e')
  
(** [get_args t] decomposes the {!type:term} [t] into a pair [(h,args)], where
    [h] is the head term of [t] and [args] is the list of arguments applied to
    [h] in [t]. The returned [h] cannot be an [Appl] node. *)
and get_args : term -> term * term list = fun t ->
  let rec get_args t acc =
    match unfold t with
    | Appl(t,u) -> get_args t (u::acc)
    | t         -> t, acc
  in get_args t []

(** [get_args_len t] is similar to [get_args t] but it also returns the length
    of the list of arguments. *)
and get_args_len : term -> term * term list * int = fun t ->
  let rec get_args_len acc len t =
    match unfold t with
    | Appl(t, u) -> get_args_len (u::acc) (len + 1) t
    | t          -> (t, acc, len)
  in
  get_args_len [] 0 t

(** [is_symb s t] tests whether [t] is of the form [Symb(s)]. *)
and is_symb : sym -> term -> bool = fun s t ->
  match unfold t with Symb(r) -> r == s | _ -> false

(* We make the equality of terms modulo commutative and
   associative-commutative symbols syntactic by always ordering arguments in
   increasing order and by putting them in a comb form.

   The term [t1 + t2 + t3] is represented by the left comb [(t1 + t2) + t3] if
   + is left associative and [t1 + (t2 + t3)] if + is right associative. *)

(** [left_aliens s t] returns the list of the biggest subterms of [t] not
   headed by [s], assuming that [s] is left associative and [t] is in
   canonical form. This is the reverse of [mk_left_comb]. *)
and left_aliens : sym -> term -> term list = fun s ->
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
and right_aliens : sym -> term -> term list = fun s ->
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
    log "right_aliens %a %a = %a" sym s term t (D.list term) r;
  r

(** [mk_Appl t u] puts the application of [t] to [u] in canonical form wrt C
   or AC symbols. *)
and mk_Appl : term * term -> term = fun (t, u) ->
  (* if Logger.log_enabled () then
    log "mk_Appl(%a, %a)" term t term u;
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
    log "mk_Appl(%a, %a) = %a" term t term u term r;
  r *)

(* For debugging purposes, [db_closed i t] checks that all free de Bruijn appearing
   in [t] are in the range [1..i]. Additionally [bv] specifies which of [1..n] are allowed to occur. *)
and _db_closed : ?bv:bool array -> int -> term -> bool =
  fun ?(bv=[||]) i t ->
  let n = Array.length bv in
  if Logger.log_enabled () then
    log "db_closed: fv(%a) in [1..%d]&[%a]" term t i pr_bound bv;
  let rec check t =
    match unfold t with
    | Db k when k>i -> raise Exit
    | Db k when k<=n && bv.(k-1)=false -> raise Exit
    | Appl(a,b) -> check a; check b
    | Abst(a,(_,_,e))
    | Prod(a,(_,_,e)) -> check a; List.iter check e
    | LLet(a,t,(_,_,e)) -> check a; check t; List.iter check e
    | Meta(_,ts)
    | Patt(_,_,ts) -> Array.iter check ts
    | _ -> ()
  in try check t; true with Exit -> false

(* unit test *)
let _ =
  let s =
    create_sym [] Privat (AC true) Eager false (Pos.none "+") None Kind [] in
  let t1 = Vari (new_var "x1") in
  let t2 = Vari (new_var "x2") in
  let t3 = Vari (new_var "x3") in
  let left = mk_bin s (mk_bin s t1 t2) t3 in
  let right = mk_bin s t1 (mk_bin s t2 t3) in
  let eq = eq_of_cmp cmp in
  assert (eq (mk_left_comb s t1 [t2; t3]) left);
  assert (eq (mk_right_comb s [t1; t2] t3) right);
  let eq = eq_of_cmp (List.cmp cmp) in
  assert (eq (left_aliens s left) [t1; t2; t3]);
  assert (eq (right_aliens s right) [t3; t2; t1])

(** [is_abst t] returns [true] iff [t] is of the form [Abst(_)]. *)
let is_abst : term -> bool = fun t ->
  match unfold t with Abst(_) -> true | _ -> false

(** [is_prod t] returns [true] iff [t] is of the form [Prod(_)]. *)
let is_prod : term -> bool = fun t ->
  (match unfold t with Prod(_) -> true | _ -> false)


(** [iter_atoms db f g t] applies f to every occurrence of a variable in t,
    g to every occurrence of a symbol, and db to every occurrence of a dB.
    We have to be careful with binders since in the current implementation
    closure environment may contain slots for variables that don't actually
    appear.
 *)
let iter_atoms : (int -> unit) -> (var -> unit) -> (sym -> unit) -> term -> unit =
  fun db f g t ->
  let rec check db t =
    match unfold t with
    | Vari x -> f x
    | Symb s -> g s
    | Db i -> db i
    | Appl(a,b) -> check db a; check db b
    | Abst(a,b)
    | Prod(a,b) -> check db a; check_binder db b
    | LLet(a,t,b) -> check db a; check db t; check_binder db b
    | Meta(_,ts)
    | Patt(_,_,ts) -> Array.iter (check db) ts
    | _ -> ()
  and check_binder db (_bi,u,e) =
    (* dBs occuring in [u], bound vars *excluded* (hence the -1 in db_u) *)
    let u_dbs = ref IntSet.empty in
    let db_u i =
      if i > 1 then u_dbs := InsSet.add (i-1) !u_ds in
    (* We check u, recording which dBs occur *)
    check db_u u;
    let n = List.length e in
    (* We then check the members of [e] that *actually* occur in u *)
    List.iteri (fun i t -> if IntSet.mem (n-i) !u_dbs then check db t) e in
  check t

let iter_atoms_mbinder
    : (int -> unit) -> (var -> unit) -> (sym -> unit) -> mbinder -> unit =
  fun dbs f g (bi,u,e) ->
    let n = Array.length bi.mbinder_bound in
    (* dBs occuring in [u], bound vars *excluded* (hence the -n in db_u) *)
    let u_dbs = ref IntSet.empty in
    let db_u i =
      if i > N then u_dbs := InsSet.add (i-n) !u_ds in
    (* We check u, recording which dBs occur *)
    iter_atoms db_u f g u;
    let m = List.length e in
    (* We then check the members of [e] that *actually* occur in u *)
    List.iteri
      (fun i t -> if IntSet.mem (m-i) !u_dbs then iter_atoms db f g t) e

(** [occur x t] tells whether variable [x] occurs in [t]. *)
let occur : var -> term -> bool =
  fun x t ->
  try iter_var_sym (fun _ ->()) (fun y -> if x==y then raise Exit) (fun _->()) t; false
  with Exit -> true

let occur_mbinder : var -> mbinder -> bool =
  fun x b ->
  try iter_atoms_mbinder (fun _ ->()) (fun y -> if x==y then raise Exit) (fun _->()) b; false
  with Exit -> true
                                           
(** [subst b v] substitutes the variable bound by [b] with the value [v].
    Assumes v is closed (since only called from outside the term library. *)
let subst : binder -> term -> term = fun (bi,t,e) v ->
  let env = Array.of_list e in
  let n = Array.length env in
  let rec subst t =
    if Logger.log_enabled() then
      log "subst [1≔%a] %a" term v term t;
    match unfold t with
    | Db k -> if k==1 then (assert bi.binder_bound; v)
              else begin
                  let j = k-1 in
                  assert (j <= n);
                  env.(n-j)
                end
    | Appl(a,b) -> mk_Appl(subst a, subst b)
    | Abst(a,(n,u,e)) -> Abst(subst a, (n, u, List.map subst e))
    | Prod(a,(n,u,e)) -> Prod(subst a, (n ,u, List.map subst e))
    | LLet(a,t,(n,u,e)) -> LLet(subst a, subst t, (n, u, List.map subst e))
    | Meta(m,ts) -> Meta(m, Array.map subst ts)
    | Patt(j,n,ts) -> Patt(j,n, Array.map subst ts)
    | _ -> t
  in
  let r =
    if bi.binder_bound = false && Array.length env = 0 then t
    else subst t in
  if Logger.log_enabled() then
    log "subst %a[%a] [%a] = %a" term t terms (Array.of_list e) term v term r;
  r

(** [unbind b] substitutes the binder [b] by a fresh variable of name [name]
   if given, or the binder name otherwise. The variable and the result of the
   substitution are returned. *)
let unbind : ?name:string -> binder -> var * term =
  fun ?(name="") ((bn,_,_) as b) ->
  let n = if name="" then bn.binder_name else name in
  let x = new_var n in x, subst b (Vari x)

(** [unbind2 f g] is similar to [unbind f], but it substitutes two binders [f]
   and [g] at once using the same fresh variable. *)
let unbind2 : ?name:string -> binder -> binder -> var * term * term =
  fun ?(name="") ((bn1,_,_) as b1) b2 ->
  let n = if name="" then bn1.binder_name else name in
  let x = new_var n in x, subst b1 (Vari x), subst b2 (Vari x)

(** [unmbind b] substitutes the multiple binder [b] with fresh variables. This
    function is analogous to [unbind] for binders. Note that the names used to
    create the fresh variables are based on those of the multiple binder. *)
let unmbind : mbinder -> var array * term =
  fun (({mbinder_name=names;_},_,_) as b) ->
  let xs = Array.init (Array.length names) (fun i -> new_var names.(i)) in
  xs, msubst b (Array.map (fun x -> Vari x) xs)
  
(** [bind_var x t] binds the variable [x] in [t], producing a binder. *)
let bind_var  : var -> term -> binder = fun ((_,n) as x) t ->
  let bound = Stdlib.ref false in
  (* Replace variables [x] by de Bruijn index [i] *)
  let rec bind i t =
    (*if Logger.log_enabled() then log "bind_var %d %a" i term t;*)
    match unfold t with
    | Vari y when y == x -> Stdlib.(bound := true); Db i
    | Appl(a,b) ->
        let a' = bind i a in
        let b' = bind i b in
        if a==a' && b==b' then t else Appl(a', b')
    (* No need to call mk_Appl here as we only replace free variables by de
       Bruijn indices. *)
    | Abst(a,b) ->
        let a' = bind i a in
        let b' = bind_binder i b in
        if a==a' && b==b' then t else Abst(a', b')
    | Prod(a,b) ->
        let a' = bind i a in
        let b' = bind_binder i b in
        if a==a' && b==b' then t else Prod(a', b')
    | LLet(a,m,b) ->
        let a' = bind i a in
        let m' = bind i m in
        let b' = bind_binder i b in
        if a==a' && m==m' && b==b' then t else LLet(a', m', b')
    | Meta(m,ts) ->
        let ts' = Array.map (bind i) ts in
        if Array.for_all2 (==) ts ts' then t else Meta(m, ts')
    | Patt(j,n,ts) ->
        let ts' = Array.map (bind i) ts in
        if Array.for_all2 (==) ts ts' then t else Patt(j,n,ts')
    | _ -> t

  and bind_binder i (n,u,e as b) =
    let e' = List.map (bind i) e in
    let j = List.length e+2 in
    (* [j] is the first unused variable: Db(1) is the variable bound by this
       binder, dB [2..|e|+1] are the variables substituted by [e], so j=|e|+2
       is the first unused variable, corresponding to a slot created at the
       head of [e] *)
    let u' = bind j u in
    if u==u' then (* If [u==u'] then x does not occur in u *)
      if List.for_all2 (==) e e' then b
      else (n, u', e')
    else (* x occurs, it has been replaced by [Db(j)],
            corresponding to the head of [e] *)
      ((*assert (_db_closed j u');*)
       (n, u', Db i::e') ) in

  (*assert (_db_closed 0 t);*)
  let b = bind 1 t in
  if Logger.log_enabled() then
    log "bind_var %a %a = %a" var x term t term b;
  (*assert (_db_closed ~bv:[|Stdlib.(!bound)|] 1 b);*)
  {binder_name=n; binder_bound=Stdlib.(!bound)}, b, []

(** [binder f b] applies f inside [b]. *)
let binder : (term -> term) -> binder -> binder = fun f b ->
  let x,t = unbind b in bind_var x (f t)

(** [bind_mvar xs t] binds the variables of [xs] in [t] to get a binder.
    It is the equivalent of [bind_var] for multiple variables. *)
let bind_mvar : var array -> term -> mbinder =
  let empty = {mbinder_name=[||]; mbinder_bound=[||]} in
  fun xs t ->
  let n = Array.length xs in
  if n = 0 then empty, t, [] else
  (*if Logger.log_enabled() then
    log "bind_mvar %a" (D.array var) xs;*)
  let map = ref IntMap.empty and mbinder_bound = Array.make n false in
  Array.iteri (fun i (ki,_) -> map := IntMap.add ki i !map) xs;
  (* Replace variables [xs.(k)] by de Bruijn index [i+k] *)
  let rec bind i t =
    (*if Logger.log_enabled() then log "bind_mvar %d %a" i term t;*)
    match unfold t with
    | Vari (key,_) ->
      begin match IntMap.find_opt key !map with
        | Some k -> mbinder_bound.(k) <- true; Db (i+k)
        | None -> t
      end
    | Appl(a,b) ->
        let a' = bind i a in
        let b' = bind i b in
        if a==a' && b==b' then t else Appl(a', b')
    (* No need to call mk_Appl here as we only replace free variables by de
       Bruijn indices. *)
    | Abst(a,b) ->
        let a' = bind i a in
        let b' = bind_binder i b in
        if a==a' && b==b' then t else Abst(a', b')
    | Prod(a,b) ->
        let a' = bind i a in
        let b' = bind_binder i b in
        if a==a' && b==b' then t else Prod(a', b')
    | LLet(a,m,b) ->
        let a' = bind i a in
        let m' = bind i m in
        let b' = bind_binder i b in
        if a==a' && m==m' && b==b' then t else LLet(a', m', b')
    | Meta(m,ts) ->
        let ts' = Array.map (bind i) ts in
        if Array.for_all2 (==) ts ts' then t else Meta(m, ts')
    | Patt(j,n,ts) ->
        let ts' = Array.map (bind i) ts in
        if Array.for_all2 (==) ts ts' then t else Patt(j,n,ts')
    | _ -> t

  (* Replace variables [xs.(k)] by de Bruijn index [i+k] *)
  and bind_binder i (bi,u,e as b) =
    (* First we bind variables in [e]. [e'] will bind indices [|bi|..|e'|+|bi|]
       (remember [1..|bi|] are the indices bound by this binder) *)
    let e' = List.map (bind i) e in
    (* If variables of xs appear in [u], they will be replaced by de Bruijn indices
       starting from [j = |e'|+2] *)
    let j = List.length e'+2 in
    (* [j] is the first unused variable: Db(1) is the variable bound by this
       binder, dB [2..|e|+1] are the variables substituted by [e], so j=|e|+2
       is the first unused variable, corresponding to a slot created at the
       head of [e] *)
    let u' = bind j u in
    if u==u' then (* If [u==u'] then none of the vars of [xs] does occur in u *)
      if List.for_all2 (==) e e' then b
      else (bi, u', e')
    else (* one var of [xs] occurs, replaced by [Db(j)..Db(j+n-1)] *)
      (let e'' =
         let rec f k e =
           if k=n then e
           else
             let t =
               (* approximation: mbinder_bound may contain true for variables
                  occuring in another subterm (i.e. not in u) *)
               if mbinder_bound.(k) then Db(i+k) else Wild in
             f (k+1) (t::e) in
         f 0 e' in
       (*assert (_db_closed (j+n-1) u');*)
       (bi, u', e'') ) in

  (*assert (_db_closed 0 t);*)
  let b = bind 1 t in
  if Logger.log_enabled() then
    log "bind_mvar %a %a = %a %a" (D.array var) xs term t pr_bound mbinder_bound term b;
  (*assert (_db_closed ~bv:mbinder_bound n b);*)
  let bi = { mbinder_name = Array.map base_name xs; mbinder_bound } in
  (* Too strong (or improve cmp) *)
  (*assert (cmp t (msubst (bi,b,[]) (Array.map (fun x->Vari x) xs)) =0);*)
  bi, b, []

(** [binder_occur b] tests whether the bound variable occurs in [b]. *)
let binder_occur : binder -> bool = fun (bi,_,_) -> bi.binder_bound
         
(** [is_closed t] checks whether [t] is closed (w.r.t. variables).
    We have to be careful with binders since in the current implementation
    closure environment may contain slots for variables that don't actually appear
 *)
let is_closed : term -> bool =
  fun t ->
  try iter_atom (fun _ -> ()) (fun _ -> raise Exit) (fun _ -> ()) t; true
  with Exit -> false

let is_closed_mbinder : mbinder -> bool =
  fun b ->
  try iter_atom_mbinder (fun _ -> ()) (fun _ -> raise Exit) (fun _ -> ()) b; true
  with Exit -> false

(** Construction functions of the private type [term]. They ensure some
   invariants:

- In a commutative function symbol application, the first argument is smaller
   than the second one wrt [cmp].

- In an associative and commutative function symbol application, the
   application is built as a left or right comb depending on the associativity
   of the symbol, and arguments are ordered in increasing order wrt [cmp].

- In [LLet(_,_,b)], [binder_occur b = true] (useless let's are erased). *)
let mk_Vari x = Vari x
let mk_Type = Type
let mk_Kind = Kind
let mk_Symb x = Symb x
let mk_Prod (a,b) = Prod (a,b)
let mk_Arro (a,b) = let x = new_var "_" in Prod(a, bind_var x b)
let mk_Abst (a,b) = Abst (a,b)
let mk_Meta (m,ts) = (*assert (m.meta_arity = Array.length ts);*) Meta (m,ts)
let mk_Patt (i,s,ts) = Patt (i,s,ts)
let mk_Wild = Wild
let mk_Plac b = Plac b
let mk_TRef x = TRef x
let mk_LLet (a,t,b) = LLet (a,t,b)

(** [mk_Appl_not_canonical t u] builds the non-canonical (wrt. C and AC
   symbols) application of [t] to [u]. WARNING: to use only in Sign.link. *)
let mk_Appl_not_canonical : term * term -> term = fun (t, u) -> Appl(t, u)

(** [add_args t args] builds the application of the {!type:term} [t] to a list
    arguments [args]. When [args] is empty, the returned value is (physically)
    equal to [t]. *)
let add_args : term -> term list -> term = fun t ts ->
  match get_args t with
  | Symb s, _ when is_modulo s ->
    List.fold_left (fun t u -> mk_Appl(t,u)) t ts
  | _ -> List.fold_left (fun t u -> Appl(t,u)) t ts

(** [add_args_map f t ts] is equivalent to [add_args t (List.map f ts)] but
   more efficient. *)
let add_args_map : term -> (term -> term) -> term list -> term = fun t f ts ->
  match get_args t with
  | Symb s, _ when is_modulo s ->
    List.fold_left (fun t u -> mk_Appl(t, f u)) t ts
  | _ -> List.fold_left (fun t u -> Appl(t, f u)) t ts

(** Patt substitution. *)
let subst_patt : mbinder option array -> term -> term = fun env ->
  let rec subst_patt t =
    match unfold t with
    | Patt(Some i,n,ts) when 0 <= i && i < Array.length env ->
      begin match env.(i) with
      | Some b -> msubst b (Array.map subst_patt ts)
      | None -> mk_Patt(Some i,n,Array.map subst_patt ts)
      end
    | Patt(i,n,ts) -> mk_Patt(i, n, Array.map subst_patt ts)
    | Prod(a,(n,b,e)) -> mk_Prod(subst_patt a, (n, subst_patt b, List.map subst_patt e))
    | Abst(a,(n,b,e)) -> mk_Abst(subst_patt a, (n, subst_patt b, List.map subst_patt e))
    | Appl(a,b) -> mk_Appl(subst_patt a, subst_patt b)
    | Meta(m,ts) -> mk_Meta(m, Array.map subst_patt ts)
    | LLet(a,t,(n,b,e)) ->
      mk_LLet(subst_patt a, subst_patt t, (n, subst_patt b, List.map subst_patt e))
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
  | Prod(a,b) -> mk_Prod(cleanup a, binder cleanup b)
  | Abst(a,b) -> mk_Abst(cleanup a, binder cleanup b)
  | Appl(a,b) -> mk_Appl(cleanup a, cleanup b)
  | Meta(m,ts) -> mk_Meta(m, Array.map cleanup ts)
  | LLet(a,t,b) -> mk_LLet(cleanup a, cleanup t, binder cleanup b)
  | Wild -> assert false
  | Plac _ -> assert false
  | TRef _ -> assert false
  | Db _ -> assert false
  | Vari _
  | Type
  | Kind
  | Symb _ -> t

(** Type of a symbol and a rule. *)
type sym_rule = sym * rule

let lhs : sym_rule -> term = fun (s, r) -> add_args (mk_Symb s) r.lhs
let rhs : sym_rule -> term = fun (_, r) -> r.rhs

(** Positions in terms in reverse order. The i-th argument of a constructor
   has position i-1. *)
type subterm_pos = int list

let subterm_pos : subterm_pos pp = fun ppf l -> D.(list int) ppf (List.rev l)

(** Type of critical pair positions (pos,l,r,p,l_p). *)
type cp_pos = Pos.popt * term * term * subterm_pos * term

(** Typing context associating a variable to a type and possibly a
    definition. The typing environment [x1:A1,..,xn:An] is represented by the
    list [xn:An;..;x1:A1] in reverse order (last added variable comes
    first). *)
type ctxt = (var * term * term option) list

let decl ppf (v,a,d) =
  out ppf "%a: %a" var v term a;
  match d with
  | None -> ()
  | Some d -> out ppf " ≔ %a" term d

let ctxt : ctxt pp = fun ppf c -> List.pp decl ", " ppf (List.rev c)

(** Type of unification constraints. *)
type constr = ctxt * term * term

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

(** Printing functions for debug. *)
module Raw = struct
  let sym = sym let _ = sym
  let term = term let _ = term
  let ctxt = ctxt let _ = ctxt
end
