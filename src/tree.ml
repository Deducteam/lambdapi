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
    conditions (see constructor {!constructor:Cond} of {!type:Tree_types.tree}
    for more details). These conditions are tested during evaluation to select
    which of the two subsequent branches to follow.

    There are two forms of conditions:
    - convertibility conditions (see {!constructor:Tree_types.CondNL}),
    - free variable conditions (see {!constructor:Tree_types.CondFV}).

    Convertibility conditions are used we have non left-linear rewriting rules
    such as [f &x &x (s &y) → r]. In this case we need to test whether the two
    terms at position [{0}] and [{1}] (corresponding to [&x]) are convertible:
    the rule can only be apply if that is the case. Note that in general there
    may be more than two occurrences of a variables. In that case we will need
    to check convertibility between more than two terms.

    Free variable constraints are used to verify which variables are free in a
    term. If there is a rule of the form [f (λ x y, &Y[y]) → &Y], then we need
    to check that the term at position [{0.0}] depends only on [y]. *)

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
    { nl_partial : int IntMap.t
    (** An association [(e, v)] is a slot [e] of the [env] array with a slot
          [v] of the [vars] array. *)
    ; nl_conds : PSet.t
    (** Set of convertibility constraints that can be checked. *)
    ; fv_conds : (tvar array) IntMap.t
    (** Set of free variable constraints. *) }

  (** {b NOTE} the integer indices stored in {!field:nl_conds} and the keys of
      in {!field:fv_conds} correspond to (valid) positions in the [vars] array
      of the {!val:Eval.tree_walk} function. *)

  (** [empty] is the condition pool holding no condition. *)
  let empty : t =
    { nl_partial = IntMap.empty
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
      pp_partials pool.nl_partial pp_available pool.nl_conds

  (** [is_empty pool] tells whether the pool of constraints is empty. *)
  let is_empty : t -> bool = fun pool ->
    PSet.is_empty pool.nl_conds && IntMap.is_empty pool.fv_conds

  (* TODO cleanup from here. *)

  (** [instantiate i d q] instantiate constraint on slot [i] in pool [q], that
      is.  Typically, if a constraint involves only one variable, then
      instantiating a variable is equivalent to instantiating a constraint.
      However, if a constraint involves several variables, then instantiating
      a variable will promote the constraint to a {e partially instantiated
      state}, and will be completely instantiated when all the variables are
      instantiated.  The [d] is some additional data needed.
      @raise Not_found if [p] is not part of any constraint in [q]. *)
  let instantiate_nl : int -> int -> t -> t = fun slot i pool ->
    let normalize (i, j) = if i < j then (i, j) else (j, i) in
    try
      let e = normalize (slot, IntMap.find i pool.nl_partial) in
      { pool with nl_conds = PSet.add e pool.nl_conds }
    with Not_found ->
      { pool with nl_partial = IntMap.add i slot pool.nl_partial }

  let instantiate_fv : int -> tvar array -> t -> t = fun i vs pool ->
    { pool with fv_conds = IntMap.add i vs pool.fv_conds }

  (** [constrained_nl slot pool] tells whether slot [slot] is constrained in
      the constraint pool [pool]. *)
  let constrained_nl : int -> t -> bool = fun slot pool ->
    IntMap.mem slot pool.nl_partial


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
    | CondNL(i,j)  ->
        let nl_conds = PSet.remove (i,j) pool.nl_conds in
        {pool with nl_conds}
    | CondFV(xs,i) ->
        try
          let ys = IntMap.find i pool.fv_conds in
          let eq = Array.equal Bindlib.eq_vars xs ys in
          if eq then {pool with fv_conds = IntMap.remove i pool.fv_conds}
          else pool
        with Not_found -> pool

  (** [choose pools] selects a condition to verify among [pools]. *)

  (** [choose e c p] chooses recursively among pools in [p] an available
      condition calling function [c] on each pool, with [e] being the function
      indicating whether a pool is empty. *)
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
    A} is a column of {e actions}.  Each line of a pattern matrix is a pattern
    to which is attached an action.  When reducing a term, if a line filters
    the term, or equivalently the term matches the pattern, the term is
    rewritten to the action. *)
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

  (** Compile time counterpart to the argument stack of the head symbol. *)
  type occur_rs = arg list

  (** Data needed to bind terms from the lhs into the rhs. *)
  type env_builder = (int * (int * term Bindlib.mvar)) list

  (** A redefinition of the rule type.

      {b Note} that {!type:array} is used while {!type:stack} could
      be used because {!val:pick_best_among} goes through all items of a rule
      anyway ([max(S) = Θ(|S|)]).  Since heuristics need to access elements of
      the matrix, we favour quick access with {!type:array}. *)
  type clause =
    { c_lhs : term array
    (** Left hand side of a rule.   *)
    ; c_rhs : rhs
    (** Right hand side of a rule. *)
    ; env_builder : env_builder
    (** Maps slots of the {!val:vars} array to a slot of the final
        environment used to build the {!field:c_rhs}. *)
    ; cond_pool : CP.t
    (** Condition pool with convertibility and free variable constraints. *) }

  (** Type of a matrix of patterns.  Each line is a row having an attached
      action. *)
  type t =
    { clauses : clause list
    (** The rules. *)
    ; slot : int
    (** Index of next slot to use in {!val:vars} array to store variables. *)
    ; positions : occur_rs
    (** Positions of the elements of the matrix in the initial term.  We rely
        on the order relation used in sets. *) }

  (** Operations embedded in the tree *)
  type decision =
    | Yield of clause
    (** Apply a clause. *)
    | Check_stack
    (** Check whether the stack is empty (used to handle multiple arities with
        the {!val:rule_order} set). *)
    | Specialise of int
    (** Further specialise the matrix against constructors of a given
        column. *)
    | Condition of tree_cond
    (** [CondNL(c, s)] indicates a non-linearity constraint on column [c] with
        respect to slot [s]. [CondFV(vs, i)] says that the free variables of
        the matched term should be among [vs]. *)

  (** [pp o m] prints matrix [m] to out channel [o]. *)
  let pp_matrix : ?pp_cond:bool -> t pp = fun ?(pp_cond=false) oc m ->
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

  (** [is_treecons t] tells whether the term [t] corresponds to a constructor
      in the sense of the module {!module:Tree_types.TC}. *)
  let is_treecons : term -> bool = fun t ->
    match fst (get_args t) with
    | Patt(_, _, _) -> false
    | Vari(_)
    | Abst(_, _)
    | Symb(_, _)    -> true
    | _             -> assert false

  (** [of_rules r] creates the initial pattern matrix from a list of rewriting
      rules. *)
  let of_rules : rule list -> t = fun rs ->
    let r2r {lhs; rhs; _} =
      { c_lhs = Array.of_list lhs ; c_rhs = rhs
      ; cond_pool = CP.empty ; env_builder = [] }
    in
    let size = (* Get length of longest rule *)
      if rs = [] then 0 else
      List.max ~cmp:Int.compare
        (List.map (fun r -> List.length r.Terms.lhs) rs) in
    let positions =
      if size = 0 then []
      else List.init (size - 1) (fun i -> {arg_path = [i]; arg_rank = 0})
    in
    { clauses = List.map r2r rs ; slot = 0 ; positions }

  (** [is_empty m] returns whether matrix [m] is empty. *)
  let is_empty : t -> bool = fun m -> m.clauses = []

  (** [get_col n m] retrieves column [n] of matrix [m]. *)
  let get_col : int -> t -> term list = fun ind m ->
    List.map (fun {c_lhs ; _} -> c_lhs.(ind)) m.clauses

  (** [score c] returns the score heuristic for column [c].  The score is a
      tuple containing the number of constructors and the number of storage
      required. *)
  let score : term list -> float = fun ts ->
    let rec loop ((ncons, nst) as acc) = function
      | []                    -> acc
      | x :: xs
        when is_treecons x    -> loop (ncons + 1, nst) xs
      | Patt(Some(_),_,_)::xs -> loop (ncons, nst + 1) xs
      | Patt(_,_,e)      ::xs
        when e <> [||]        -> loop (ncons, nst + 1) xs
      | _ :: xs               -> loop acc xs
    in
    let nc, ns = loop (0, 0) ts in
    float_of_int nc /. (float_of_int ns)

  (** [pick_best_among m c] returns the index of the best column of matrix [m]
      among columns [c] according to a heuristic. *)
  let pick_best_among : t -> int array -> int = fun mat columns->
    let scores = Array.map (fun ci -> score (get_col ci mat)) columns in
    Array.max_index ~cmp:(Pervasives.compare) scores

  (** [can_switch_on r k] returns whether a switch can be carried out on
      column [k] of clauses [r]. *)
  let can_switch_on : clause list -> int -> bool = fun  clauses k ->
    List.for_all (fun r -> Array.length r.c_lhs >= k + 1) clauses &&
    List.exists (fun r -> is_treecons r.c_lhs.(k)) clauses

  (** [discard_cons_free r] returns the list of indexes of columns containing
      terms that can be matched against (discard constructor-free columns) in
      clauses [r]. *)
  let discard_cons_free : clause list -> int array = fun clauses ->
    let ncols = List.max ~cmp:Int.compare
        (List.map (fun {c_lhs ; _} -> Array.length c_lhs) clauses)
    in
    let switchable = List.init ncols (can_switch_on clauses) in
    let switchable2ind i e = if e then Some(i) else None in
    Array.of_list (List.filteri_map switchable2ind switchable)

  (** [choose m] returns the index of column to switch on. *)
  let choose : t -> int option = fun m ->
    let kept = discard_cons_free m.clauses in
    if kept = [||] then None else
    let sel_partial = pick_best_among m kept in
    Some(kept.(sel_partial))

  (** [is_exhausted p r] returns whether [r] can be applied or not, with [p]
      the occurrences of the terms in [r]. *)
  let is_exhausted : occur_rs -> clause -> bool =
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
      Array.for_all2 check lhs de
      && nonl lhs
    in
    CP.is_empty cond_pool && (lhs = [||] || ripe lhs)

  (** [yield m] yields a clause to be applied. *)
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

  (** [get_cons l] extracts, sorts and uniqify terms that are tree
      constructors in [l].  The actual tree constructor (of type
      {!type:treecons}) is returned along the original term. *)
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

  (** [store m c d] returns whether the inspected term on column [c] of matrix
      [m] needs to be stored during evaluation. *)
  let store : t -> int -> bool = fun cm ci ->
    let (_, a, _) = List.destruct cm.positions ci in
    let st_r r =
      match r.c_lhs.(ci) with
      | Patt(Some(_), _, _) -> true
      | Patt(_, _, e)       -> Array.length e < a.arg_rank
      | _                   -> false
    in
    List.exists st_r cm.clauses

  (** [update_aux c v r] returns clause [r] with auxiliary data updated
      (i.e. non linearity constraints and environment builder) when inspecting
      column [c] having met [v] vars until now. *)
  let update_aux : int -> int -> occur_rs -> clause -> clause =
    fun ci slot pos r ->
    let (_, a, _) = List.destruct pos ci in
    let t = r.c_lhs.(ci) in
    match fst (get_args t) with
    | Patt(i, _, e) ->
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

  (** [specialize p c s r] specializes the clauses [r] when matching pattern
      [p] against column [c] with positions [s].  A matrix can be specialized
      by a user defined symbol.  In case an {!constructor:Appl} is given as
      pattern [p], only terms having the same number of arguments and the same
      leftmost {e non} {!constructor:Appl} term match. *)
  let specialize : term -> int -> occur_rs -> clause list ->
    occur_rs * clause list = fun pat ci pos rs ->
    let pos =
      let l, m, r = List.destruct pos ci in
      let _, _, nargs = get_args_len pat in
      let replace =
        if nargs = 0 then [] else
        List.init (nargs - 1) (fun i -> {m with arg_path = i :: m.arg_path})
      in
      List.reconstruct l replace r
    in
    let ph, pargs, lenp = get_args_len pat in
    let insert r e = Array.concat [ Array.sub r.c_lhs 0 ci
                                  ; e
                                  ; Array.drop (ci + 1) r.c_lhs ]
    in
    let filtrans r =
      let insert = insert r in
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

  (** [default c s r] computes the default clauses from [r] that remain to be
      matched in case the pattern used is not in the column [c]. [s] is the
      list of positions of the elements in each clause. *)
  let default : int -> occur_rs -> clause list -> occur_rs * clause list =
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

  (** [abstract c v p r] computes the clauses resulting from the
      specialisation by an abstraction.  Note that the pattern can't be an
      applied lambda since the lhs is in normal form. *)
  let abstract : int -> tvar -> occur_rs -> clause list ->
                 occur_rs * clause list =
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
  let empty_stack : clause list -> occur_rs * clause list = fun cs ->
    ([], List.filter (fun r -> r.c_lhs = [||]) cs)

  (** [not_empty_stack c] keeps the not empty clauses from [c]. *)
  let not_empty_stack : clause list -> clause list =
    List.filter (fun r -> r.c_lhs <> [||])
end

(** [harvest l r e s] exhausts linearly the stack composed only of pattern
    variables with no non linear constraints. *)
let harvest : term array -> rhs -> CM.env_builder -> int -> tree =
    fun lhs rhs env_builder slot ->
  let default_node store child =
    Node { swap = 0 ; store ; children = TCMap.empty
         ; abstraction = None ; default = Some(child) }
  in
  let rec loop lhs env_builder slot = match lhs with
    | []                        -> Leaf(env_builder, rhs)
    | Patt(Some(i), _, e) :: ts ->
        let env_builder = (slot, (i, Array.map to_tvar e)) :: env_builder in
        let slot = slot + 1 in
        default_node true (loop ts env_builder slot)
    | Patt(None, _, _) :: ts    ->
        default_node false (loop ts env_builder slot)
    | _                         -> assert false in
  loop (Array.to_list lhs) env_builder slot

(** {b NOTE} the compiling step builds a decision tree (which can then be used
    for pattern matching). A tree guides the pattern matching by:
    - accepting constructors and filtering possible clauses,
    - performing as few atomic matchings as possible (by considering the  most
      appropriate term in the argument stack),
    - storing terms that may be needed in the RHS because they match a pattern
      variable constructor {!constructor:Patt} in the {!field:lhs} field.

    The first bullet is ensured using {!val:CM.specialize},  {!val:CM.default}
    and {!val:CM.abstract}, which allow to create new branches.

    Efficiency is managed thanks to heuristics handled by the {!val:score}
    function.

    The last is managed by the {!val:env_builder} as follows.  The evaluation
    process used two arrays, one containing elements, as binders, to be
    injected in the {!field:c_rhs}, and another one to memorise terms filtered
    by a pattern variable {!constructor:Patt}.  A memorised term can be used
    either to check a constraint, or to be copied in the aforementioned array.
    The former is called the [env] array while the latter is the [vars] array.
    To copy correctly the variables from the [vars] to the [env] array, each
    clause has an {!val:env_builder} mapping a index in the [vars] array to a
    slot in the [env] (the slot [i] of a [Patt(Some(i), _, _)]).  Note that
    the [vars] array can contain terms that are useless for the clause that is
    applied, as terms might have been saved because needed by another clause
    which is not the one applied.  The {!field:slot} keeps track of how many
    variables have been encountered so far and thus indicates the index in
    [vars] that will be used by the next variable. *)

(** [compile m] translates the given pattern matching problem,  encoded by the
    matrix [m], into a decision tree. *)
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
        let ncm = CM.{clauses ; slot ; positions } in
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
