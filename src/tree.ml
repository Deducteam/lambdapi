(** Compilation of rewriting rules to decision trees.

    This module handles the compilation of rewriting rules to “decision trees”
    based on the method described by Luc Maranget.

    @see <https://doi.org/10.1145/1411304.1411311> *)

open Timed
open Extra
open Terms
open Basics
open Tree_types

(** Flag indicating whether the order of rules in files should be preserved by
    decision trees. *)
let rule_order : bool Pervasives.ref = Pervasives.ref false

(** {1 Types for decision trees}

    The types involved in the definition of decision trees are given in module
    {!module:Tree_types} (they could not be defined here as this would lead to
    a cyclic dependency).

    {b Example:} let us consider the rewrite system for symbol [f] defined as:
    - [f Z     (S m) → S m],
    - [f n     Z     → n] and
    - [f (S n) (S m) → S (S m)].

    A possible decision tree might be
    {v
    ├─?─∘─Z─∘     → n
    ├─Z─∘─Z─∘     → n
    │   └─S─∘─?─∘ → S m
    ├─S─∘─Z─∘     → n
    └─S─∘─?─∘     → S (S m)
    v}
    with [∘] being a node (with an omitted label) and [─u─] being an edge with
    a matching on symbol [u] or a variable or wildcard when [?]. Typically the
    portion [S─∘─Z] is made possible by a swap. *)

(** Representation of a rewriting rule RHS (or action) as given in the type of
    rewriting rules (see {!field:Terms.rhs}). In decision trees, we will store
    a RHS in every leaf since they correspond to matched rules. *)
type rhs = (term_env, term) Bindlib.mbinder

(** Representation of a branching condition (see {!type:Terms.tree_cond}). *)
type tree_cond = term Tree_types.tree_cond

(** Representation of a tree (see {!type:Terms.tree}). *)
type tree = (term, rhs) Tree_types.tree

(** {1 Conditions for decision trees}

    The decision trees used for pattern matching include binary nodes carrying
    conditions (see constructor {!constructor:Tree_types.tree.Cond}) that must
    be tested during evaluation to select which of the two subsequent branches
    to follow. There are two forms of conditions:
    - convertibility conditions ({!constructor:Tree_types.tree_cond.CondNL}),
    - free variable conditions ({!constructor:Tree_types.tree_cond.CondFV}).

    Convertibility conditions are used whenever we try to apply a rule that is
    not left-linear, for example [f &x &x (s &y) → r]. In this case we need to
    test whether the two terms at position [{0}] and [{1}] (that correspond to
    pattern variable [&x]) are convertible: the rule may only apply if that is
    the case. Note that in general there may be more than two occurrences of a
    variable, so we may need to check convertibility several times.

    Free variable constraints are used to verify which variables are free in a
    term. If there is a rule of the form [f (λ x y, &Y[y]) → &Y], then we need
    to check that the term at position [{0.0}] does not depend on [x] (or that
    among [x] and [y], only [y] is allowed). *)

(** Module providing a representation for pools of conditions. *)
module CP = struct
  (** Functional sets of pairs of integers. *)
  module PSet = Set.Make(
    struct
      type t = int * int

      let compare : t -> t -> int = fun (i1,i2) (j1,j2) ->
        match i1 - j1 with 0 -> i2 - j2 | k -> k
    end)

  (** A pool of (convertibility and free variable) conditions. *)
  type t =
    { variables : int IntMap.t
    (** An association [(e, v)] maps the slot of a pattern variable (the first
        argument of a {!constructor:Terms.term.Patt}) to its slot in the array
        [vars] of the {!val:Eval.tree_walk} function. It is used to remember
        non linearity constraints. *)
    ; nl_conds : PSet.t
    (** Set of convertibility constraints.  Convertibility constraint [(i, j)]
        is satisfied when the terms stored at indices [i] and [j] in the array
        [vars] of the {!val:Eval.tree_walk} function are convertible.*)
    ; fv_conds : (tvar array) IntMap.t
    (** A mapping of [i] to [xs] represents a free variable condition that can
        only be satisfied if only the free variables of [x] appear in the term
        stored at slot [i] in the [vars] array of {!val:Eval.tree_walk}. *) }

  (** [empty] is the condition pool holding no condition. *)
  let empty : t =
    { variables = IntMap.empty
    ; nl_conds = PSet.empty
    ; fv_conds = IntMap.empty }

  (** [pp oc pool] prints condition pool [pool] to channel [oc]. *)
  let pp : t pp = fun oc pool ->
    let pp_fv oc fv_conds =
      let pp_sep oc () = Format.pp_print_string oc ";" in
      let pp_tvs = Format.pp_print_list ~pp_sep Print.pp_tvar in
      let ppit oc (a, b) =
        Format.fprintf oc "@[(%a@@%d)@]" pp_tvs (Array.to_list b) a
      in
      let pp_sep oc () = Format.pp_print_string oc "::" in
      Format.fprintf oc "@[<v>@[%a@]@]"
        (Format.pp_print_list ~pp_sep ppit) (IntMap.bindings fv_conds)
    in
    let pp_partials oc partials =
      let pp_sep oc _ = Format.pp_print_string oc ";" in
      let pp_part oc (i, j) = Format.fprintf oc "@[(%d↦%d)@]" i j in
      Format.fprintf oc "@[<h>%a@]" (Format.pp_print_list ~pp_sep pp_part)
        (IntMap.bindings partials)
    in
    let pp_available oc available =
      let pp_av oc (i, j) = Format.fprintf oc "@[%d≡%d@]" i j in
      let pp_sep = Format.pp_print_cut in
      Format.fprintf oc "@[<hov>%a@]" (Format.pp_print_list ~pp_sep pp_av)
        (PSet.elements available)
    in
    Format.fprintf oc "@[<hov>%a/@,%a/@,%a@]" pp_fv pool.fv_conds
      pp_partials pool.variables pp_available pool.nl_conds

  (** [is_empty pool] tells whether the pool of constraints is empty. *)
  let is_empty : t -> bool = fun pool ->
    PSet.is_empty pool.nl_conds && IntMap.is_empty pool.fv_conds

  (** [instantiate_nl slot_v slot_e pool] instantiates a convertibility
      constraint between slots [slot_v] and [slot_e] in pool [pool].  The
      instantiation of a convertibility constraint is done in two parts.
      Remember that a non linearity constraints involve two or more variables,
      that have different slots [slot_v] in the [vars] array but share the
      same slot [slot_e] in the final environment (the one of the
      {!type:rhs}).  Assume arguments [sv1 se p], and that there is no
      variable using slot [se] yet in pool [p].  Then a constraint involving
      [sv1] will be partially instantiated.  If the function is called again
      with [sv2 se p], then the variable at slot [sv2] (of [vars]) uses slot
      [se] as well and must therefore be convertible with the previous
      variable.  A convertibility condition between [sv1] and [sv2] is thus
      fully instantiated and can be checked. *)
  let instantiate_nl : int -> int -> t -> t = fun slot i pool ->
    let normalize (i, j) = if i < j then (i, j) else (j, i) in
    try
      let e = normalize (slot, IntMap.find i pool.variables) in
      { pool with nl_conds = PSet.add e pool.nl_conds }
    with Not_found -> (* If there is no variable constrained with environment
                         slot [i] in [pool.variables] yet. *)
      { pool with variables = IntMap.add i slot pool.variables }

  (** [instantiate_fv slot xs pool] activates a free variables condition
      regarding variables in [xs] on slot [slot] of the [vars] array in pool
      [pool]. *)
  let instantiate_fv : int -> tvar array -> t -> t = fun i vs pool ->
    { pool with fv_conds = IntMap.add i vs pool.fv_conds }

  (** [constrained_nl slot pool] tells whether slot [slot] is constrained in
      the constraint pool [pool]. *)
  let constrained_nl : int -> t -> bool = fun slot pool ->
    IntMap.mem slot pool.variables

  (** [is_instantiated cond pool] tells whether the condition [cond] has  been
      instantiated in the pool [pool] *)
  let is_instantiated cond pool =
    match cond with
    | CondNL(i,j) -> PSet.mem (i,j) pool.nl_conds
    | CondFV(x,i) ->
        try Array.equal Bindlib.eq_vars x (IntMap.find i pool.fv_conds)
        with Not_found -> false

  (** [remove cond pool] removes condition [cond] from the pool [pool]. *)
  let remove cond pool =
    match cond with
    | CondNL(i,j)  -> {pool with nl_conds = PSet.remove (i,j) pool.nl_conds}
    | CondFV(xs,i) ->
        try
          let ys = IntMap.find i pool.fv_conds in
          let eq = Array.equal Bindlib.eq_vars xs ys in
          if eq then {pool with fv_conds = IntMap.remove i pool.fv_conds}
          else pool
        with Not_found -> pool

  (** [choose pools] selects a condition to verify among [pools]. The
      heuristic is to select in priority a convertibility constraint. *)
  let choose : t list -> tree_cond option = fun pools ->
    let rec choose_nl pools =
      let export (i,j) = CondNL(i, j) in
      match pools with
      | []      -> None
      | p :: ps -> try Some(export (PSet.choose p.nl_conds))
                   with Not_found -> choose_nl ps
    in
    let rec choose_vf pools =
      let export (i,vs) = CondFV(vs,i) in
      match pools with
      | []      -> None
      | p :: ps -> try Some(export (IntMap.choose p.fv_conds))
                   with Not_found -> choose_vf ps
    in
    let res = choose_nl pools in
    if res = None then choose_vf pools else res
end


(** {1 Clause matrix and pattern matching problem} *)

(** {b NOTE} we ideally need the {!type:stack} of terms used during evaluation
    (argument [stk] of {!val:Eval.tree_walk}) to provide fast element access
    (for swaps) as well as fast {!val:Extra.List.destruct} and
    {!val:Extra.List.reconstruct} (to inspect a particular element, reduce it,
    and then reinsert it). In practice, the naive representation based on
    lists is faster than more elaborate solutions, unless there are rules with
    {e many} arguments.  Alternatives to a list-based implementation would be
    cat-enable lists / deques, finger trees (Paterson & Hinze) or random
    access lists. In the current implementation, [destruct e i] has a time
    complexity of [Θ(i)] and [reconstruct l m r] has a time complexity of
    [Θ(length l + length m)]. *)

(** A clause matrix encodes a pattern matching problem.  The clause matrix {i
    C} can be denoted {i C = P → A} where {i P} is a {e pattern matrix} and {i
    A} is a column of {e rhs}.  Each line of a pattern matrix is a pattern to
    which is attached a rhs.  When reducing a term, if a line filters the
    term, or equivalently the term matches the pattern, the term is rewritten
    to the rhs. *)
module CM = struct
  (** Representation of a subterm in argument position in a pattern. *)
  type arg =
    { arg_path : int list (** Reversed path to the subterm. *)
    ; arg_rank : int      (** Number of abstractions along the path. *) }

  (** {b NOTE} the {!field:arg_path} describes a path to the represented term.
      The idea is that each index of the list tells under which argument to go
      next (counting from [0]), starting from the end of the list. For example
      let us consider the term [f x (g a b)]. The subterm [a] is accessed with
      the path [[0 ; 1]] (go under the second argument [g a b] first, and then
      take its first argument). Similarly, [b] is encoded as [[1 ; 1]] and [x]
      as [[0]]. Note that a value [[]] does not describe a valid path. Also, a
      [0] index is used when going under abstractions. In that case, the field
      {!field:arg_rank} is incremented. *)

  (** Data needed to bind terms from the lhs into the rhs. An element
      [(sv, (se, xs))] indicates that slot [sv] of the [vars] array will be
      bound into slot [se] of the environment using free variables [xs]. *)
  type env_builder = (int * (int * term Bindlib.mvar)) list

  (** A row of a clause matrix, composed of a lhs, a rhs, a pool of conditions
      and some auxiliary data, can be schematized as
      [c_lhs → c_rhs if cond_pool] *)
  type clause =
    { c_lhs : term array
    (** Left hand side of a rule. *)
    ; c_rhs : rhs
    (** Right hand side of a rule. *)
    ; env_builder : env_builder
    (** Data needed to build the substitution from terms matched by the lhs to
        the rhs. *)
    ; cond_pool : CP.t
    (** Condition pool with convertibility and free variable constraints. *) }

  (** Type of clause matrices. *)
  type t =
    { clauses : clause list
    (** The rules. *)
    ; slot : int
    (** Index of next slot to use in [vars] array to store variables. *)
    ; positions : arg list
    (** Positions of the elements of the matrix in the initial term.  We rely
        on the order relation used in sets. *) }

  (** Available operations on clause matrices.  Each operation is an
      evaluation decision. *)
  type decision =
    | Yield of clause
    (** Rewrite to a rhs when a lhs filters the input. *)
    | Check_stack
    (** Check whether the stack is empty (used to handle multiple arities with
        the {!val:rule_order} set). *)
    | Specialise of int
    (** Further specialise the matrix against constructors on a given
        column. *)
    | Condition of tree_cond
    (** [CondNL(c, s)] indicates a non-linearity constraint on column [c] with
        respect to slot [s]. [CondFV(vs, i)] says that the free variables of
        the matched term should be among [vs]. *)

  (** [pp ?(pp_cond=false) o m] prints matrix [m] to out channel [o].  If
      [pp_cond] is true, writes the condition pools as well. *)
  let pp : ?pp_cond:bool -> t pp = fun ?(pp_cond=false) oc m ->
    let pp_lhs oc lhs =
      Format.fprintf oc "@[%a → … @]" (Array.pp Print.pp " | ") lhs
    in
    let pp_path oc l =
      if l = [] then Format.fprintf oc "ε" else
        List.pp (fun oc -> Format.fprintf oc "%d") "·" oc (List.rev l)
    in
    let out fmt = Format.fprintf oc fmt in
    let lp = List.map (fun a -> a.arg_path) m.positions in
    let lr = List.map (fun a -> a.arg_rank) m.positions in
    let llhs = List.map (fun cl -> cl.c_lhs) m.clauses in
    let cut = Format.pp_print_cut in
    out "@[<v 0>### Matrix start ###@,";
    out "@[<h>%s: @[%a@]@]@,"
      "Positions" (List.pp pp_path ";") lp;
    out "@[<h>@<9>%s: @[%a@]@]@,"
      "Depths" (List.pp Format.pp_print_int ";") lr;
    out "@[<v 0>%a@]@," (Format.pp_print_list ~pp_sep:cut pp_lhs) llhs;
    if pp_cond then
      begin
        let lcp = List.map (fun cl -> cl.cond_pool) m.clauses in
        out "@[<v 0>%a@]@," (Format.pp_print_list ~pp_sep:cut CP.pp) lcp
      end;
    out "### Matrix end   ###@]@."

  (** [is_treecons t] returns whether the term [t] corresponds to a
      constructor (see {!type:Tree_types.TC.t}) against which a specialisation
      can be carried out. *)
  let is_treecons : term -> bool = fun t ->
    match fst (get_args t) with
    | Patt(_, _, _) -> false
    | Vari(_)
    | Abst(_, _)
    | Symb(_, _)    -> true
    | _             -> assert false

  (** [of_rules r] transforms a set of rewriting rules into a clause matrix
      rules. *)
  let of_rules : rule list -> t = fun rs ->
    let r2r {lhs; rhs; _} =
      let c_lhs = Array.of_list lhs in
      { c_lhs ; c_rhs = rhs ; cond_pool = CP.empty ; env_builder = [] }
    in
    let size = (* Get length of longest rule *)
      if rs = [] then 0 else
      List.max ~cmp:Int.compare (List.map (fun r -> Terms.(r.arity)) rs)
    in
    let positions =
      if size = 0 then [] else
      List.init (size - 1) (fun i -> {arg_path = [i]; arg_rank = 0})
    in
    { clauses = List.map r2r rs ; slot = 0 ; positions }

  (** [is_empty m] returns whether matrix [m] is empty.  Note that a matrix is
      empty when it has {e no} row; not when it has empty rows. *)
  let is_empty : t -> bool = fun m -> m.clauses = []

  (** [get_col n m] retrieves column [n] of matrix [m]. *)
  let get_col : int -> t -> term list = fun ind m ->
    List.map (fun {c_lhs ; _} -> c_lhs.(ind)) m.clauses

  (** [score c] returns the score heuristic for column [c].  The score is the
      number of tree constructors divided by the number of conditions. *)
  let score : term list -> float = fun ts ->
    let rec loop ((ncons, nst) as acc) = function
      | []                           -> acc
      | x :: xs when is_treecons x   -> loop (ncons + 1, nst) xs
      | Patt(Some(_),_,_)::xs        -> loop (ncons, nst + 1) xs
      | Patt(_,_,e)::xs when e <> [||] -> loop (ncons, nst + 1) xs
      | _ :: xs                      -> loop acc xs
    in
    let nc, ns = loop (0, 0) ts in
    float_of_int nc /. (float_of_int ns)

  (** [pick_best_among m c] returns the index of the best column of matrix [m]
      among columns [c].  "Best" in the sense of the heuristic implemented in
      {!val:score}. *)
  let pick_best_among : t -> int array -> int = fun mat columns->
    let scores = Array.map (fun ci -> score (get_col ci mat)) columns in
    Array.max_index ~cmp:(Pervasives.compare) scores

  (** [can_switch_on r k] returns whether a switch can be carried out on
      column [k] of list of clauses [r]. *)
  let can_switch_on : clause list -> int -> bool = fun  clauses k ->
    List.for_all (fun r -> Array.length r.c_lhs >= k + 1) clauses &&
    List.exists (fun r -> is_treecons r.c_lhs.(k)) clauses

  (** [discard_cons_free r] returns the indexes of columns that contain terms
      with symbols on top among clauses [r].  These terms allow to
      {!val:specialize} on the column. *)
  let discard_cons_free : clause list -> int array = fun clauses ->
    let ncols =
      let arities = List.map (fun cl -> Array.length cl.c_lhs) clauses in
      List.max ~cmp:Int.compare arities
    in
    let switchable = List.init ncols (can_switch_on clauses) in
    let switchable2ind i e = if e then Some(i) else None in
    Array.of_list (List.filteri_map switchable2ind switchable)

  (** [choose m] returns the index of column to switch on. *)
  let choose : t -> int option = fun m ->
    let kept = discard_cons_free m.clauses in
    if kept = [||] then None else Some(kept.(pick_best_among m kept))

  (** [is_exhausted p c] returns whether clause [r] whose terms are at
      positions in [p] can be applied or not. *)
  let is_exhausted : arg list -> clause -> bool =
    fun positions {c_lhs = lhs ; cond_pool ; _} ->
    let nonl lhs =
      (* Verify that there are no non linearity constraints in the remaining
         terms.  We must check that there are no constraints in the remaining
         terms and no constraints left partially instantiated. *)
      let slots =
        let fn t = match t with Patt(i,_,_) -> i | _ -> None in
        List.filter_map fn (Array.to_list lhs)
      in
      let slots_uniq = List.sort_uniq Int.compare slots in
      let fn s = CP.constrained_nl s cond_pool in
      List.same_length slots slots_uniq && not (List.exists fn slots_uniq)
    in
    let depths = Array.of_list (List.map (fun i -> i.arg_rank) positions) in
    let ripe lhs =
      (* [ripe l] returns whether [lhs] can be applied. *)
      let de = Array.sub depths 0 (Array.length lhs) in
      let check pt de =
      (* We verify that there are no variable constraints, that is, if
         abstractions are traversed, then variable must be allowed in pattern
         variables. *)
        match pt with
        | Patt(_, _, e) -> Array.length e = de
        | _             -> false
      in
      Array.for_all2 check lhs de && nonl lhs
    in
    CP.is_empty cond_pool && (lhs = [||] || ripe lhs)

  (** [yield m] returns the next operation to carry out on matrix [m], that
      is, either specialising, solving a constraint or rewriting to a rule. *)
  let yield : t -> decision = fun ({ clauses ; positions ; _ } as m) ->
    (* If a line is empty and priority is given to the topmost rule, we have
       to eliminate ¨empty¨ rules. *)
    if Pervasives.(!rule_order)
       && List.exists (fun x -> x.c_lhs = [||]) clauses
       && List.exists (fun x -> x.c_lhs <> [||]) clauses
    then Check_stack else
    try
      if Pervasives.(!rule_order) then
        let fc = List.hd clauses in
        if is_exhausted positions fc then Yield(fc) else raise Not_found
      else let r = List.find (is_exhausted positions) clauses in
      Yield(r)
    with Not_found ->
      (* Here is the heuristic: process in priority specialisations, then
         convertibility constraints, then closedness constraints. *)
      match choose m with
      | Some(c) -> Specialise(c)
      | None    ->
      match CP.choose (List.map (fun r -> r.cond_pool) m.clauses) with
      | Some(c) -> Condition(c)
      | None    -> Specialise(0)

  (** [get_cons l] returns a list of unique (and sorted) tuples containing
      tree construcors and the original term. *)
  let get_cons : term list -> (TC.t * term) list = fun telst ->
    let keep_treecons e =
      let h, _, arity = get_args_len e in
      match h with
      | Symb({ sym_name ; sym_path ; _ }, _) ->
          Some(TC.Symb(arity, sym_name, sym_path), e)
      | Abst(_, _)                           -> Some(Abst, e)
      | Vari(x)                              ->
          Some(Vari(Bindlib.name_of x), e)
      | _                                    -> None
    in
    let tc_fst_cmp (tca, _) (tcb, _) = TC.compare tca tcb in
    List.sort_uniq tc_fst_cmp (List.filter_map keep_treecons telst)

  (** [store m c] is true iff a term of column [c] of matrix [m] contains a
      pattern variable.  In that case, the term needs to be stored into the
      [vars] array (in order to build the substitution). *)
  let store : t -> int -> bool = fun cm ci ->
    let (_, a, _) = List.destruct cm.positions ci in
    let st_r r =
      match r.c_lhs.(ci) with
      | Patt(Some(_), _, _) -> true
      | Patt(_, _, e)       -> Array.length e < a.arg_rank
      | _                   -> false
    in
    List.exists st_r cm.clauses

  (** [update_aux col slot clause] updates the fields the condition pool and
      the environment builder of clause [clause] assuming column [col] is
      inspected and the next environment slot is [slot]. *)
  let update_aux : int -> int -> arg list -> clause -> clause =
    fun ci slot pos r ->
    match fst (get_args r.c_lhs.(ci)) with
    | Patt(i, _, e) ->
        let (_, a, _) = List.destruct pos ci in
        let cond_pool =
          if (Array.length e) <> a.arg_rank then
            CP.instantiate_fv slot (Array.map to_tvar e) r.cond_pool
          else r.cond_pool
        in
        let cond_pool =
          match i with
          | Some(i) -> CP.instantiate_nl slot i cond_pool
          | None    -> cond_pool
        in
        let env_builder =
          match i with
          | Some(i) -> (slot, (i, Array.map to_tvar e)) :: r.env_builder
          | None    -> r.env_builder
        in
        { r with env_builder ; cond_pool }
    | _             -> r

  (** [specialize pat col pos cl] filters and transforms lhs of [cl] assuming
      a matching on pattern [pat] on column [col], with [pos] being the
      position of arguments in clauses. *)
  let specialize : term -> int -> arg list -> clause list ->
    arg list * clause list = fun pat ci pos rs ->
    let pos =
      let l, m, r = List.destruct pos ci in
      let _, _, nargs = get_args_len pat in
      let replace =
        if nargs = 0 then [] else
        List.init (nargs - 1) (fun i -> {m with arg_path = i :: m.arg_path})
      in
      List.reconstruct l replace r
    in
    let insert r e = Array.concat [ Array.sub r.c_lhs 0 ci
                                  ; e
                                  ; Array.drop (ci + 1) r.c_lhs ]
    in
    let filtrans r =
      let insert = insert r in
      let ph, pargs, lenp = get_args_len pat in
      let h, args, lenh = get_args_len r.c_lhs.(ci) in
      match ph, h with
      | Symb(_, _), Symb(_, _)
      | Vari(_)   , Vari(_)       ->
          if lenh = lenp && Basics.eq ph h
          then Some({r with c_lhs = insert (Array.of_list args)})
          else None
      | _         , Patt(_, _, _) ->
          let arity = List.length pargs in
          let e = Array.make arity (Patt(None, "", [||])) in
          Some({ r with c_lhs = insert e })
      | _         , Abst(_, _)    -> None
      | _         , _             -> assert false
    in
    (pos, List.filter_map filtrans rs)

  (** [default col pos cl] selects and transforms clauses [cl] assuming that
      terms on column [col] does not match any symbol being the head structure
      of another term in column [col]; [pos] is the positions of terms in
      clauses. *)
  let default : int -> arg list -> clause list -> arg list * clause list =
    fun ci pos rs ->
    let pos =
      let (l, _, r) = List.destruct pos ci in
      List.rev_append l r
    in
    let transf r =
      match r.c_lhs.(ci) with
      | Patt(_, _, _)           ->
          let c_lhs = Array.append
              (Array.sub r.c_lhs 0 ci)
              (Array.drop (ci + 1) r.c_lhs) in
          Some({r with c_lhs})
      | Symb(_, _) | Abst(_, _)
      | Vari(_)    | Appl(_, _) -> None
      | _ -> assert false in
    (pos, List.filter_map transf rs)

  (** [abstract col var pos cl] selects and transforms clauses [cl] assuming
      that terms in column [col] match an abstraction.  The term under the
      abstraction has its bound variable substituted by [var]; [pos] is the
      position of terms in clauses [cl]. *)
  let abstract : int -> tvar -> arg list -> clause list ->
                 arg list * clause list =
    fun ci v pos clauses ->
    let (l, {arg_path; arg_rank}, r) = List.destruct pos ci in
    let a = {arg_path = 0 :: arg_path; arg_rank = arg_rank + 1} in
    let pos = List.rev_append l (a :: r) in
    let insert r e = [ Array.sub r.c_lhs 0 ci
                     ; [| e |]
                     ; Array.drop (ci + 1) r.c_lhs ]
    in
    let transf (r:clause) =
      let ph, pargs = get_args r.c_lhs.(ci) in
      match ph with
      | Abst(_, b)           ->
          assert (pargs = []) ; (* Patterns in β-normal form *)
          let b = Bindlib.subst b (mkfree v) in
          Some({r with c_lhs = Array.concat (insert r b)})
      | Patt(_, _, _) as pat ->
          Some({r with c_lhs = Array.concat (insert r pat)})
      | Symb(_, _) | Vari(_) -> None
      | _                    -> assert false
    in
    (pos, List.filter_map transf clauses)

  (** [cond_ok cond cls] updates the clause list [cls] assuming that condition
      [cond] is satisfied. *)
  let cond_ok : tree_cond -> clause list -> clause list = fun cond ->
    List.map (fun r -> {r with cond_pool = CP.remove cond r.cond_pool})

  (** [cond_fail cond cls]  updates the clause list [cls] with the information
      that the condition [cond] is not satisfied. *)
  let cond_fail : tree_cond -> clause list -> clause list = fun cond ->
    List.filter (fun r -> not (CP.is_instantiated cond r.cond_pool))

  (** [empty_stack c] keeps the empty clauses from [c]. *)
  let empty_stack : clause list -> arg list * clause list = fun cs ->
    ([], List.filter (fun r -> r.c_lhs = [||]) cs)

  (** [not_empty_stack c] keeps the not empty clauses from [c]. *)
  let not_empty_stack : clause list -> clause list =
    List.filter (fun r -> r.c_lhs <> [||])
end

(** [harvest l r e s] exhausts linearly the lhs [l] composed only of pattern
    variables with no constraints, to yield a leaf with rhs [r], environment
    builder [e] completed. *)
let harvest : term array -> rhs -> CM.env_builder -> int -> tree =
    fun lhs rhs env_builder slot ->
  let default_node store child =
    Node { swap = 0 ; store ; children = TCMap.empty
         ; abstraction = None ; default = Some(child) }
  in
  let rec loop lhs env_builder slot =
    match lhs with
    | []                        -> Leaf(env_builder, rhs)
    | Patt(Some(i), _, e) :: ts ->
        let env_builder = (slot, (i, Array.map to_tvar e)) :: env_builder in
        default_node true (loop ts env_builder (slot + 1))
    | Patt(None, _, _) :: ts    ->
        default_node false (loop ts env_builder slot)
    | _                         -> assert false in
  loop (Array.to_list lhs) env_builder slot

(** {b NOTE} {!val:compile} produces a decision tree from a set of rewriting
    rules (in practice, they all belong to a same symbol).  This tree is
    designed to be used in the reduction process, in function
    {!val:Eval.tree_walk}.  The purpose of the trees is to
    - declare efficiently whether the input term (during evaluation) matches
      some lhs from the orginal rules (the one from which the tree is built);
    - build a substitution mapping some (sub) terms of the input term to the
      rewritten term.

    The first bullet is handled by the definition of the trees, e.g. if a
    switch node contains in its mapping a tree constructor [s], then terms
    having (as head structure) symbol [s] will be accepted.

    The second bullet is managed by the environment builder of type
    {!type:CM.env_builder}.  If a lhs contains a named pattern variable, then
    it is used in the rhs.  To do that, the term is saved into an array of
    terms [vars].  When the leaf is reached, the terms from that array are
    copied into the rhs.  The instructions to save terms are in the field
    {!field:CM.store}.  The instructions to copy adequately terms from [vars]
    to the rhs are in an environment builder (of type
    {!type:CM.env_builder}). *)

(** [compile m] translates the pattern matching problem encoded by the matrix
    [m] into a decision tree. *)
let rec compile : CM.t -> tree = fun ({clauses ; positions ; slot} as pats) ->
  if CM.is_empty pats then Fail else
  match CM.yield pats with
  | Yield({c_rhs ; env_builder ; c_lhs ; _}) ->
      if c_lhs = [||] then Leaf(env_builder, c_rhs) else
      harvest c_lhs c_rhs env_builder slot
  | Condition(cond)                          ->
      let ok   = compile {pats with clauses = CM.cond_ok   cond clauses} in
      let fail = compile {pats with clauses = CM.cond_fail cond clauses} in
      Cond({ok ; cond ; fail})
  | Check_stack                              ->
      let left =
        let positions, clauses = CM.empty_stack clauses in
        compile {pats with clauses; positions}
      in
      let right = compile {pats with clauses = CM.not_empty_stack clauses} in
      Eos(left, right)
  | Specialise(swap)                         ->
      let store = CM.store pats swap in
      let updated = List.map (CM.update_aux swap slot positions) clauses in
      let slot = if store then slot + 1 else slot in
      let cons = CM.get_cons (CM.get_col swap pats) in
      (* Constructors specialisation *)
      let children =
        let fn acc (tr_cons, te_cons) =
          if tr_cons = TC.Abst then acc else
          let (positions, clauses) =
            CM.specialize te_cons swap positions updated
          in
          TCMap.add tr_cons (compile CM.{clauses ; slot ; positions}) acc
        in
        List.fold_left fn TCMap.empty cons
      in
      (* Default child *)
      let default =
        let (positions, clauses) = CM.default swap positions updated in
        let ncm = CM.{clauses ; slot ; positions} in
        if CM.is_empty ncm then None else Some(compile ncm)
      in
      (* Abstraction specialisation*)
      let abstraction =
        if List.for_all (fun (x, _) -> x <> TC.Abst) cons then None else
        let var = Bindlib.new_var mkfree "tr" in
        let (positions, clauses) = CM.abstract swap var positions updated in
        Some(var, compile CM.{clauses ; slot ; positions})
      in
      Node({swap ; store ; children ; abstraction ; default})

(** [update_dtree s] updates decision tree of symbol [s]. *)
let update_dtree : sym -> unit = fun symb ->
  let tree = lazy (compile (CM.of_rules !(symb.sym_rules))) in
  let cap = lazy (Tree_types.tree_capacity (Lazy.force tree)) in
  symb.sym_tree := (cap, tree)
