(** Compilation of rewriting rules to decision trees.

    This module handles the compilation of rewriting rules to “decision trees”
    based on the method described by Luc Maranget.

    @see <https://dblp.uni-trier.de/rec/html/conf/ml/Maranget08> *)

open Lplib open Base open Extra
open Common
open Timed
open Term
open LibTerm
open Tree_type

let log = Logger.make 'd' "tree" "compilation of decision trees"
let log = log.pp

(** {1 Types for decision trees}

    The types involved in the definition of decision trees are given in module
    {!module:Tree_type} (they could not be defined here as this would lead to
    a cyclic dependency).

    {b Example:} let us consider the rewrite system for symbol [f] defined as:
    - [f Z     (S m) ↪ S m],
    - [f n     Z     ↪ n] and
    - [f (S n) (S m) ↪ S (S m)].

    A possible decision tree might be
    {v
    ├─?─∘─Z─∘     ↪ n
    ├─Z─∘─Z─∘     ↪ n
    │   └─S─∘─?─∘ ↪ S m
    ├─S─∘─Z─∘     ↪ n
    └─S─∘─?─∘     ↪ S (S m)
    v}
    with [∘] being a node (with an omitted label) and [─u─] being an edge with
    a matching on symbol [u] or a variable or wildcard when [?]. Typically the
    portion [S─∘─Z] is made possible by a swap. *)

(** Representation of a tree (see {!type:Tree_type.tree}). *)
type tree = rule Tree_type.tree

(** {1 Conditions for decision trees}

    The decision trees used for pattern matching include binary nodes carrying
    conditions (see constructor {!constructor:Tree_type.tree.Cond}) that must
    be tested during evaluation to select which of the two subsequent branches
    to follow. There are two forms of conditions:
    - convertibility conditions ({!constructor:Tree_type.tree_cond.CondNL}),
    - free variable conditions ({!constructor:Tree_type.tree_cond.CondFV}).

    Convertibility conditions are used whenever we try to apply a rule that is
    not left-linear, for example [f $x $x (s $y) ↪ r]. In this case we need to
    test whether the two terms at position [{0}] and [{1}] (that correspond to
    pattern variable [$x]) are convertible: the rule may only apply if that is
    the case. Note that in general there may be more than two occurrences of a
    variable, so we may need to check convertibility several times.

    Free variable constraints are used to verify which variables are free in a
    term. If there is a rule of the form [f (λ x y, $Y[y]) ↪ $Y], then we need
    to check that the term at position [{0.0}] does not depend on [x] (or, put
    in other words, that among [x] and [y], only [y] is allowed). *)

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
        argument of a {!constructor:Term.term.Patt}) to its slot in the array
        [vars] of the {!val:Eval.tree_walk} function. It is used to remember
        non linearity constraints. *)
    ; nl_conds : PSet.t
    (** Set of convertibility constraints [(i,j)] with [i < j]. The constraint
        [(i,j)] is satisfied if the terms stored at indices [i] and [j] in the
        [vars] array of the {!val:Eval.tree_walk} function are convertible. *)
    ; fv_conds : int array IntMap.t
    (** A mapping of [i] to [xs] represents a free variable condition that can
        only be satisfied if only the free variables of [x] appear in the term
        stored at slot [i] in the [vars] array of {!val:Eval.tree_walk}. *) }

  (** [empty] is the condition pool holding no condition. *)
  let empty : t =
    { variables = IntMap.empty
    ; nl_conds = PSet.empty
    ; fv_conds = IntMap.empty }

  (** [is_empty pool] tells whether the pool of constraints is empty. *)
  let is_empty : t -> bool = fun pool ->
    PSet.is_empty pool.nl_conds && IntMap.is_empty pool.fv_conds

  (** [register_nl slot i pool] registers the fact that the slot [slot] in the
      [vars] array correspond to a term stored at index [i] in the environment
      for the RHS. The first time that such a slot is associated to [i], it is
      registered to serve as a reference point for testing convertibility when
      (and if) another such slot is (ever) encountered. When that is the case,
      a convertibility constraint is registered between the term stored in the
      slot [slot] and the term stored in the reference slot. *)
  let register_nl : int -> int -> t -> t = fun slot i pool ->
    try
      (* We build a new condition if there is already a point of reference. *)
      let cond = (IntMap.find i pool.variables, slot) in
      { pool with nl_conds = PSet.add cond pool.nl_conds }
    with Not_found ->
      (* First occurence of [i], register the slot as a point of reference. *)
      { pool with variables = IntMap.add i slot pool.variables }

  (** [register_fv slot xs pool] registers a free variables constraint for the
      variables in [xs] on the slot [slot] of the [vars] array in [pool]. *)
  let register_fv : int -> int array -> t -> t = fun i vs pool ->
    { pool with fv_conds = IntMap.add i vs pool.fv_conds }

  (** [constrained_nl i pool] tells whether index [i] in the RHS's environment
      has already been associated to a variable of the [vars] array. *)
  let constrained_nl : int -> t -> bool = fun slot pool ->
    IntMap.mem slot pool.variables

  (** [is_contained cond pool] tells whether the condition [cond] is contained
      in the pool [pool]. *)
  let is_contained : tree_cond -> t -> bool = fun cond pool ->
    match cond with
    | CondNL(i,j) -> PSet.mem (i,j) pool.nl_conds
    | CondFV(i,x) ->
        try Array.eq (=) x (IntMap.find i pool.fv_conds)
        with Not_found -> false

  (** [remove cond pool] removes condition [cond] from the pool [pool]. *)
  let remove cond pool =
    match cond with
    | CondNL(i,j)  -> {pool with nl_conds = PSet.remove (i,j) pool.nl_conds}
    | CondFV(i,xs) ->
        try
          let ys = IntMap.find i pool.fv_conds in
          if not (Array.eq (=) xs ys) then pool
          else {pool with fv_conds = IntMap.remove i pool.fv_conds}
        with Not_found -> pool

  (** [choose pools] selects a condition to check in the pools of [pools]. The
      heuristic is to first select convertibility constraints. *)
  let choose : t list -> tree_cond option = fun pools ->
    let rec choose_nl pools =
      let export (i,j) = CondNL(i, j) in
      match pools with
      | []      -> None
      | p :: ps -> try Some(export (PSet.choose p.nl_conds))
                   with Not_found -> choose_nl ps
    in
    let rec choose_vf pools =
      let export (i,vs) = CondFV(i,vs) in
      match pools with
      | []      -> None
      | p :: ps -> try Some(export (IntMap.choose p.fv_conds))
                   with Not_found -> choose_vf ps
    in
    let res = choose_nl pools in
    if res = None then choose_vf pools else res
end

(** {1 Clause matrix and pattern matching problem} *)

(** {b NOTE} We ideally need the type [stack] of terms used during evaluation
    (argument [stk] of {!val:Eval.tree_walk}) to have fast element access (for
    swaps) as well as fast destruction and reconstruction operations (for more
    information on these operations have a look at  {!val:Lplib.List.destruct}
    and {!val:Lplib.List.reconstruct}).  These operations are intuitively used
    to inspect a particular element, reduce it, and then reinsert it. It seems
    that in practice,  the naive representation based on lists performs better
    than more elaborate solutions, unless there are rules with many arguments.
    Alternatives to a list-based implementation would be cat-enable lists  (or
    deques), finger trees (Paterson & Hinze) or random access lists.  With the
    current implementation, [destruct e i] has a time complexity of [Θ(i)] and
    [reconstruct l m r] has a time complexity of [Θ(length l + length m)]. *)

(** Clause matrices encode pattern matching problems.  The clause matrix {i C}
    can be denoted {i C = P ↪ A} where {i P} is a {e pattern matrix} and {i A}
    is a column of {e RHS}.  Each line of a matrix is a pattern to which a RHS
    is attached. When reducing a term,  if a line filters the term  (i.e., the
    term matches the pattern) then term is rewritten to the RHS. *)
module CM = struct
  (** [head ppf t] prints head of term [t]. *)
  let head : term pp = fun ppf t ->
    string ppf
      ( match get_args t with
        | Symb s, _ -> s.sym_name
        | Patt _, _ -> "$"
        | Vari _, _ -> "x"
        | Abst _, _ -> "λ"
        | Prod _, _ -> "Π"
        | _ -> assert false (* Terms that souldn't appear in lhs *) )

  (** Representation of a subterm in argument position in a pattern. *)
  type arg =
    { arg_path : int list (** Reversed path to the subterm. *)
    ; arg_rank : int      (** Number of binders along the path. *) }

  (** [arg_path ppf pth] prints path [pth] as a dotted list of integers to
      formatter [ppf]. *)
  let arg_path : int list pp = fun ppf pth ->
    out ppf "{%a}" (List.pp int ".") (List.rev pth)

  (** {b NOTE} the {!field:arg_path} describes a path to the represented term.
      The idea is that each index of the list tells under which argument to go
      next (counting from [0]), starting from the end of the list. For example
      let us consider the term [f x (g a b)]. The subterm [a] is accessed with
      the path [[0 ; 1]] (go under the second argument [g a b] first, and then
      take its first argument). Similarly, [b] is encoded as [[1 ; 1]] and [x]
      as [[0]]. Note that a value [[]] does not describe a valid path. Also, a
      [0] index is used when going under abstractions. In that case, the field
      {!field:arg_rank} is incremented. *)

  (** A clause matrix row (schematically {i c_lhs ↪ c_rhs if cond_pool}). *)
  type clause =
    { c_lhs       : term array
    (** Left hand side of a rule. *)
    ; c_rhs       : rule
    (** Right hand side of a rule, and number of extra variables. *)
    ; c_subst     : rhs_substit
    (** Substitution of RHS variables. *)
    ; xvars_nb    : int
    (** Number of extra variables in the rule RHS. *)
    ; cond_pool   : CP.t
    (** Condition pool with convertibility and free variable constraints. *) }

  (** [clause ppf c] pretty prints clause [c] to formatter [ppf]. *)
  let clause : clause pp = fun ppf {c_lhs; _} ->
    out ppf "| @[<h>%a@] |"
      (List.pp head " | ") (Array.to_list c_lhs)

  (** Type of clause matrices. *)
  type t =
    { clauses   : clause list
    (** The rules. *)
    ; slot      : int
    (** Index of next slot to use in [vars] array to store variables. *)
    ; positions : arg list
    (** Positions of the elements of the matrix in the initial term.
        We must have [length positions = max {length cl | cl ∈ clauses}]. *) }

  (** [pp ppf cm] pretty prints clause matrix [cm] to formatter [ppf]. *)
  let pp : t pp = fun ppf {clauses; _} ->
    out ppf "[@[<v>%a@]]"
      Format.(pp_print_list ~pp_sep:pp_print_space clause) clauses

  (** Available operations on clause matrices. Every operation corresponds to
      decision made during evaluation. This type is not used outside of the
      compilation process. *)
  type decision =
    | Yield of clause
    (** Rewrite to a RHS when a LHS filters the input. *)
    | Check_stack
    (** Check whether the stack is empty (used to handle multiple arities with
        the sequential strategy set). *)
    | Specialise of int
    (** Specialise the matrix against constructors on a given column. *)
    | Condition of tree_cond
    (** Binary decision on the result of the test of a condition.  A condition
        [CondNL(c, s)] indicates a non-linearity constraint on column [c] with
        respect to slot [s]. A condition [CondFV(vs, i)] corresponds to a free
        variable condition: only variables of [vs] are in the matched term. *)

  (** [is_treecons t] tells whether term [t] corresponds to a constructor (see
      {!type:Tree_type.TC.t}) that is a candidate for a specialization. *)
  let is_treecons : term -> bool = fun t ->
    match fst (get_args t) with
    | Patt(_) -> false
    | Vari(_)
    | Abst(_)
    | Prod(_)
    | Symb(_) -> true
    | _       -> assert false

  (** [of_rules rs] transforms rewriting rules [rs] into a clause matrix. *)
  let of_rules : rule list -> t = fun rs ->
    let r2r ({lhs; xvars_nb; _} as c_rhs) =
      let c_lhs = Array.of_list lhs in
      { c_lhs; c_rhs; cond_pool = CP.empty; c_subst = []; xvars_nb }
    in
    let size = (* Get length of longest rule *)
      if rs = [] then 0 else
      List.max ~cmp:Int.compare (List.map (fun r -> Term.(r.arity)) rs)
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

  (** [score c] returns the score heuristic for column [c].  This score is the
      number of tree constructors divided by the number of conditions. *)
  let score : term list -> float = fun ts ->
    let rec loop ((ncons, nst) as acc) = function
      | []                             -> acc
      | x :: xs when is_treecons x     -> loop (ncons + 1, nst) xs
      | Patt(Some(_),_,_)::xs          -> loop (ncons, nst + 1) xs
      | Patt(_,_,e)::xs when e <> [||] -> loop (ncons, nst + 1) xs
      | _ :: xs                        -> loop acc xs
    in
    let nc, ns = loop (0, 0) ts in
    float_of_int nc /. (float_of_int ns)

  (** [discard_cons_free r] returns the indexes of columns on which a
      specialisation can be performed. They are the columns with at least one
      symbol as head term. *)
  let discard_cons_free : clause list -> int array = fun clauses ->
    let ncols =
      let arities = List.map (fun cl -> Array.length cl.c_lhs) clauses in
      List.max ~cmp:Int.compare arities
    in
    let switchable =
      (* [can_switch_on k] is true if a switch can be performed on col [k]. *)
      let can_switch_on k =
        List.for_all (fun r -> Array.length r.c_lhs >= k + 1) clauses &&
        List.exists (fun r -> is_treecons r.c_lhs.(k)) clauses
      in
      List.init ncols can_switch_on in
    let switchable2ind i e = if e then Some(i) else None in
    Array.of_list (List.filteri_map switchable2ind switchable)

  (** [choose m] returns the index of column to switch on. *)
  let choose : t -> int option = fun m ->
    let kept = discard_cons_free m.clauses in
    if kept = [||] then None else
      (* Select the "best" (with higher [score]) column. *)
      let best =
        let scores = Array.map (fun ci -> score (get_col ci m)) kept in
        Array.max_index ~cmp:Stdlib.compare scores
      in
      Some(kept.(best))

  (** [is_exhausted p c] tells whether clause [r] whose terms are at positions
      in [p] can be applied or not. *)
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
  let yield : match_strat -> t -> decision =
    fun mstrat ({ clauses ; positions ; _ } as m) ->
    (* If a line is empty and priority is given to the topmost rule, we have
       to eliminate ¨empty¨ rules. *)
    if mstrat = Sequen
       && List.exists (fun x -> x.c_lhs = [||]) clauses
       && List.exists (fun x -> x.c_lhs <> [||]) clauses
    then Check_stack else
    try
      if mstrat = Sequen then
        (* [List.hd] won't fail because if the matrix is empty, then we don't
           enter the function (see {!val:compile}). If it is not, then it has
           at least one clause. *)
        let fc = List.hd clauses in
        if is_exhausted positions fc then Yield(fc) else raise Not_found
      else
        let r = List.find (is_exhausted positions) clauses in
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

  (** [get_cons id l] returns a list of unique (and sorted) tuples containing
      tree construcors from [l] and the original term. Variables are assigned
      id [id]. *)
  let get_cons : int VarMap.t -> term list -> (TC.t * term) list =
    fun vars_id telst ->
    let keep_treecons e =
      let h, _, arity = get_args_len e in
      match h with
      | Symb({sym_name; sym_path; _}) ->
          Some(TC.Symb(sym_path, sym_name, arity), e)
      | Vari(x)                       ->
          Some(TC.Vari(VarMap.find x vars_id), e)
      | _                             -> None
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

  let index_var : int VarMap.t -> term -> int = fun vi t ->
    VarMap.find (to_tvar t) vi

  (** [mk_wildcard vs] creates a pattern variable that accepts anything and in
      which variables [vs] can appear free. There is no order on [vs] because
      such created wildcard are not bound anywhere, so terms filtered by such
      wildcards are not kept. *)
  let mk_wildcard : VarSet.t -> term = fun vs ->
    let env = vs |> VarSet.to_seq |> Seq.map mk_Vari |> Array.of_seq in
    mk_Patt (None, "", env)

  (** [update_aux col mem clause] the condition pool and the substitution of
      clause [clause] assuming that column [col] is inspected and [mem]
      subterms have to be memorised. *)
  let update_aux : int -> int -> arg list -> int VarMap.t -> clause ->
    clause = fun ci mem pos vi r ->
    match fst (get_args r.c_lhs.(ci)) with
    | Patt(i, _, e) ->
        let (_, a, _) = List.destruct pos ci in
        let cond_pool =
          if (Array.length e) <> a.arg_rank then
            CP.register_fv mem (Array.map (index_var vi) e) r.cond_pool
          else r.cond_pool
        in
        let cond_pool =
          match i with
          | Some(i) ->
              if Logger.log_enabled () then
                log "Registering non linearity constraint on position [%a] \
                     on %d"
                  arg_path a.arg_path i;
              CP.register_nl mem i cond_pool
          | None    -> cond_pool
        in
        let c_subst =
          (* REVIEW: patterns may have slots in the RHS although they are not
             bound. *)
          (* If the pattern has a slot, either it is used in the RHS, in which
             case a  tuple [(j,vs)] consisting of  the index [j] to  which the
             matched term is bound in the  binder of the RHS and the variables
             making up the  environment of the term (if any)  as indexes among
             the  variables  collected.  Or  the  variable  is  subject  to  a
             non-linearity  constraint. In  this case, it is added to the
             substitution only if the substitution does not already contain
             a variable bound to slot [i]. *)
          let se i (_,(j,_)) = i = j in
          match i with
          | Some(i) when not (List.exists (se i) r.c_subst) ->
              (mem, (i, Array.map (index_var vi) e)) :: r.c_subst
          | _ -> r.c_subst
        in
        {r with c_subst; cond_pool}
    | _ -> r

  (** [specialize free_vars pat col pos cls] filters and transforms LHS of
      clauses [cls] whose column [col] contain a pattern that can filter
      elements filtered by pattern [pat], with [pos] being the position of
      arguments in clauses and [free_vars] is the set of variables that can
      appear free in patterns. *)
  let specialize : VarSet.t -> term -> int -> arg list -> clause list ->
    arg list * clause list = fun free_vars pat col pos cls ->
    let pos =
      let l, m, r = List.destruct pos col in
      let _, _, nargs = get_args_len pat in
      let replace =
        if nargs = 0 then [] else
        List.init (nargs - 1) (fun i -> {m with arg_path = i :: m.arg_path})
      in
      List.reconstruct l replace r
    in
    let insert r e = Array.concat [ Array.sub r.c_lhs 0 col
                                  ; e
                                  ; Array.drop (col + 1) r.c_lhs ]
    in
    let filtrans r =
      let insert = insert r in
      let ph, pargs, lenp = get_args_len pat in
      let h, args, lenh = get_args_len r.c_lhs.(col) in
      match ph, h with
      | Symb(f), Symb(g) ->
          if lenh = lenp && f == g
          then Some({r with c_lhs = insert (Array.of_list args)})
          else None
      | Vari(x), Vari(y) ->
          if lenh = lenp && eq_vars x y
          then Some({r with c_lhs = insert (Array.of_list args)})
          else None
      | _      , Patt(_) ->
          let arity = List.length pargs in
          let e = Array.make arity (mk_wildcard free_vars) in
          Some({ r with c_lhs = insert e })
      | Symb(_), Vari(_)
      | Vari(_), Symb(_)
      | _      , Prod(_)
      | _      , Abst(_) -> None
      | _      , _       -> assert false
          (* Term matched (in this case) should not appear in matrices. *)
    in
    (pos, List.filter_map filtrans cls)

  (** [default col pos cls] selects and transforms clauses [cls] assuming that
      terms on column [col] does not match any symbol being the head structure
      of another term in column [col]; [pos] is the positions of terms in
      clauses. *)
  let default : int -> arg list -> clause list -> arg list * clause list =
    fun col pos cls ->
    let pos =
      let (l, _, r) = List.destruct pos col in
      List.rev_append l r
    in
    let transf r =
      match r.c_lhs.(col) with
      | Patt(_)           ->
          let c_lhs =
            Array.append
              (Array.sub r.c_lhs 0 col)
              (Array.drop (col + 1) r.c_lhs)
          in
          Some({r with c_lhs})
      | Prod(_)
      | Symb(_) | Abst(_)
      | Vari(_) | Appl(_) -> None
      | _ -> assert false in
    (pos, List.filter_map transf cls)

  (** [binder get free_vars col v pos cls] selects and transforms clauses
      [cls] assuming that each term [t] in column [col] is a binder such that
      [get t] returns [Some(a, b)]. The term [b] under the binder has its
      bound variable substituted by [v]; [pos] is the position of terms in
      clause [cls]. The domain [a] of the binder and [b[v/x]] are put back
      into the stack (in that order), with [a] with argument position 0 and
      [b[v/x]] as argument 1. *)
  let binder : (term -> (term * tbinder)) -> VarSet.t -> int ->
    tvar -> arg list -> clause list -> arg list * clause list =
    fun get free_vars col v pos cls ->
    let (l, {arg_path; arg_rank}, r) = List.destruct pos col in
    let ab = {arg_path = 1 :: arg_path; arg_rank = arg_rank + 1} in
    let at = {arg_path = 0 :: arg_path; arg_rank} in
    let pos = List.rev_append l (at :: ab :: r) in
    let insert r e =
      Array.concat [ Array.sub r.c_lhs 0 col; e
                   ; Array.drop (col + 1) r.c_lhs ]
    in
    let transf (r:clause) =
      let ph, pargs = get_args r.c_lhs.(col) in
      match ph with
      | Patt(_)  ->
          let domain = mk_wildcard free_vars in
          let body = mk_wildcard (VarSet.add v free_vars) in
          Some{r with c_lhs = insert r [|domain; body|]}
      | Symb(_)
      | Vari(_)  -> None
      | t        ->
          let (a, b) = get t in
          assert (pargs = []) ; (* Patterns in β-normal form *)
          let b = subst b (mk_Vari v) in
          Some({r with c_lhs = insert r [|a; b|]})

    in
    (pos, List.filter_map transf cls)

  (** [abstract free_vars col v pos cls] selects and transforms clauses [cls]
      keeping lines whose column [col] is able to filter an abstraction. The
      body of the abstraction has its bound variable substituted by [v]; [pos]
      is the position of terms in clauses [cls] and [free_vars] is the set of
      {e free} variables introduced by other binders that may appear in
      patterns. *)
  let abstract : VarSet.t -> int -> tvar -> arg list -> clause list ->
    arg list * clause list =
    binder (function Abst(a,b) -> a, b | _ -> assert false)

  (** [product free_vars col v pos cls] is like [abstract free_vars col v pos
      cls] for products. *)
  let product : VarSet.t -> int -> tvar -> arg list -> clause list ->
    arg list * clause list =
    binder (function Prod(a, b) -> a, b | _ -> assert false)

  (** [cond_ok cond cls] updates the clause list [cls] assuming that condition
      [cond] is satisfied. *)
  let cond_ok : tree_cond -> clause list -> clause list = fun cond ->
    List.map (fun r -> {r with cond_pool = CP.remove cond r.cond_pool})

  (** [cond_fail cond cls]  updates the clause list [cls] with the information
      that the condition [cond] is not satisfied. *)
  let cond_fail : tree_cond -> clause list -> clause list = fun cond ->
    List.filter (fun r -> not (CP.is_contained cond r.cond_pool))

  (** [empty_stack c] keeps the empty clauses from [c]. *)
  let empty_stack : clause list -> arg list * clause list = fun cs ->
    ([], List.filter (fun r -> r.c_lhs = [||]) cs)

  (** [not_empty_stack c] keeps the not empty clauses from [c]. *)
  let not_empty_stack : clause list -> clause list =
    List.filter (fun r -> r.c_lhs <> [||])
end

(** [harvest lhs rhs subst vi slot] exhausts linearly the LHS [lhs]
    composed only  of pattern variables with  no constraints, to yield  a leaf
    with RHS [rhs]  and the substitution [subst] (which is completed). Mapping
    [vi] contains variables that may appear free in patterns. [slot] is the
    number of subterms that must be memorised. *)
let harvest :
    term array -> rule -> rhs_substit -> int VarMap.t -> int -> tree =
  fun lhs r subst vi slot ->
  let default_node store child =
    Node { swap = 0 ; store ; children = TCMap.empty
         ; abstraction = None ; product = None ; default = Some(child) }
  in
  let rec loop lhs subst slot =
    match lhs with
    | []                    -> Leaf(subst, r)
    | Patt(Some(i),_,e)::ts ->
        let subst =
          (slot, (i, Array.map (CM.index_var vi) e)) :: subst
        in
        default_node true (loop ts subst (slot + 1))
    | Patt(None,_,_)::ts    -> default_node false (loop ts subst slot)
    | _                     -> assert false
  in
  loop (Array.to_list lhs) subst slot

(** {b NOTE} {!val:compile} produces a decision tree from a set of rewriting
    rules (in practice, they all belong to a same symbol). This tree is
    designed to be used in the reduction process, in function
    {!val:Eval.tree_walk}. The purpose of the trees is to
    - declare efficiently whether the input term (during evaluation) matches
      some LHS from the orginal rules (the one from which the tree is built);
    - build a substitution mapping some (sub) terms of the filtered term to
      the rewritten term.

    The first bullet is handled by the definition of the trees, e.g. if a
    switch node contains in its mapping a tree constructor [s], then terms
    having (as head structure) symbol [s] will be accepted.

    The second bullet is managed by the substitution of type
    {!type:Tree_type.rhs_substit}. If a LHS contains a named pattern variable,
    then it
    is used in the RHS. Sub-terms that are filtered by named variables that
    are bound in the RHS are saved into an array during evaluation. When a
    leaf is reached, the substitution is applied on the RHS, copying terms
    from that array to the RHS. Subterms are saved into the array when field
    [store] of nodes is true. *)

(** [compile mstrat m] translates the pattern matching problem encoded by the
    matrix [m] into a decision tree following strategy [mstrat]. *)
let compile : match_strat -> CM.t -> tree = fun mstrat m ->
  (* [compile count vars_id cm] compiles clause matrix [cm]. The mapping
     [vars_id] maps variables bound in the pattern (either by abstractions
     [Abst] or products [Prod]) that may appear free in patterns to integers.
     Outermost variable is tagged 0, and hence variables are represented with
     DeBruijn levels. *)
  let rec compile : int VarMap.t -> CM.t -> tree =
  fun vars_id ({clauses; positions; slot} as cm) ->
  if CM.is_empty cm then Fail else
  let compile_cv = compile vars_id in
  if Logger.log_enabled () then log "Compile@ %a" CM.pp cm;
  match CM.yield mstrat cm with
  | Yield({c_rhs; c_subst; c_lhs; _}) ->
      harvest c_lhs c_rhs c_subst vars_id slot
  | Condition(cond)                        ->
      if Logger.log_enabled () then log "Condition [%a]" tree_cond cond;
      let ok   = compile_cv {cm with clauses = CM.cond_ok   cond clauses} in
      let fail = compile_cv {cm with clauses = CM.cond_fail cond clauses} in
      Cond({ok; cond; fail})
  | Check_stack                            ->
      if Logger.log_enabled () then log "Check stack";
      let left =
        let positions, clauses = CM.empty_stack clauses in
        compile_cv {cm with clauses; positions}
      in
      let right = compile_cv {cm with clauses=CM.not_empty_stack clauses} in
      Eos(left, right)
  | Specialise(swap)                       ->
      if Logger.log_enabled () then log "Swap on column %d" swap;
      let store = CM.store cm swap in
      let updated =
        List.map (CM.update_aux swap slot positions vars_id) clauses
      in
      let slot = if store then slot + 1 else slot in
      let column = CM.get_col swap cm in
      let cons = CM.get_cons vars_id column in
      (* Get variables of a [VarMap]. *)
      let keys m = VarMap.to_seq m |> Seq.map fst |> VarSet.of_seq in
      (* Constructors specialisation *)
      let children =
        let fn acc (tr_cons, te_cons) =
          let (positions, clauses) =
            CM.specialize (keys vars_id) te_cons swap positions updated
          in
          TCMap.add tr_cons (compile_cv CM.{clauses ; slot ; positions}) acc
        in
        List.fold_left fn TCMap.empty cons
      in
      (* Default child *)
      let default =
        let (positions, clauses) = CM.default swap positions updated in
        let ncm = CM.{clauses; slot; positions} in
        if CM.is_empty ncm then None else Some(compile_cv ncm)
      in
      let binder recon mat_transf =
        if List.for_all (fun x -> not (recon x)) column then None else
        let v_lvl = VarMap.cardinal vars_id in (* Level of the variable. *)
        let var = new_tvar (Printf.sprintf "d%dv" v_lvl) in
        let (positions, clauses) =
          mat_transf (keys vars_id) swap var positions updated
        in
        (* Add [var] to the variables that may appear free in patterns. *)
        let vars_id = VarMap.add var v_lvl vars_id in
        let next =
          compile vars_id CM.{clauses; slot; positions}
        in
        Some(v_lvl, next)
      in
      let abstraction = binder is_abst CM.abstract in
      let product = binder is_prod CM.product in
      Node({swap ; store ; children ; abstraction ; default; product})
  in
  compile VarMap.empty m

(** [update_dtree s rs] updates the decision tree of the symbol [s] by adding
   rules [rs]. *)
let update_dtree : sym -> rule list -> unit = fun symb rs ->
  let rs = if rs = [] then !(symb.sym_rules) else !(symb.sym_rules) @ rs in
  let cm = lazy (CM.of_rules rs) in
  let tree = lazy (compile symb.sym_mstrat (Lazy.force cm)) in
  let cap = lazy (Tree_type.tree_capacity (Lazy.force tree)) in
  symb.sym_dtree := (cap, tree)
