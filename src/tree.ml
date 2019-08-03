(** Compilation of rewriting rules to decision trees.

    This module handles the compilation of rewriting rules to “decision trees”
    based on the method described by Luc Maranget.

    @see <https://doi.org/10.1145/1411304.1411311> *)

open Timed
open Extra
open Terms
open Basics
open Tree_types

(** Priority on topmost rule if set to true. *)
let rule_order : bool Pervasives.ref = Pervasives.ref false

(** {3 Conditions for decision trees}

    The decision trees used for pattern matching include binary nodes carrying
    conditions (see constructor {!constructor:Cond} of
    {!type:Tree_types.tree}). We test these conditions during evaluation to
    choose which branch to follow. We have two forms of conditions in the
    current implementation.
    - convertibility conditions (see module {!module:NLCond} below),
    - free variable conditions (see module {!module:FVCond} below). *)

(** [choose e c p] chooses recursively among pools in [p] an available
    condition calling function [c] on each pool, with [e] being the function
    indicating whether a pool is empty. *)
let rec choose : ('a -> bool) -> ('a -> 'b) -> 'a list -> 'b option =
  fun m_is_empty m_choose ps ->
  match ps with
  | h :: t ->
      if m_is_empty h then choose m_is_empty m_choose t else Some(m_choose h)
  | []     -> None

(** Signature for a pool of conditions. Conditions are added on the fly during
    the construction of decision trees. Constraints can involve one or several
    patterns from a rewriting rule LHS (see {!val:instantiate}). *)
module type Cond_sig = sig
  (** Pool of constraints. *)
  type t

  (** Representation of an (instantiated) condition. *)
  type cond

  (** Auxiliary data used to instantiate a condition. *)
  type data

  (** Synonym of {!type:cond}, made concrete in the interface. *)
  type exported

  (** [pp oc pool] prints the pool [pool] to channel [oc]. *)
  val pp : t pp

  (** [pp_cond oc cond] prints condition [cond] to channel [oc]. *)
  val pp_cond : cond pp

  (** Empty set of conditions. *)
  val empty : t

  (** [is_empty pool] tells whether the pool [pool] is empty. *)
  val is_empty : t -> bool

  (** [instantiate i d q] instantiate constraint on slot [i] in pool [q], that
      is.  Typically, if a constraint involves only one variable, then
      instantiating a variable is equivalent to instantiating a constraint.
      However, if a constraint involves several variables, then instantiating
      a variable will promote the constraint to a {e partially instantiated
      state}, and will be completely instantiated when all the variables are
      instantiated.  The [d] is some additional data needed.
      @raise Not_found if [p] is not part of any constraint in [q]. *)
  val instantiate : int -> data -> t -> t

  (** [is_instantiated cond pool] tells whether the condition [cond] has  been
      instantiated in the pool [pool] *)
  val is_instantiated : cond -> t -> bool

  (** [remove cond pool] removes condition [cond] from the pool [pool]. *)
  val remove : cond -> t -> t

  (** [export cond] returns the exported counterpart of [cond]. *)
  val export : cond -> exported

  (** [choose pools] selects a condition to verify among [pools]. *)
  val choose : t list -> cond option
end

(** Module providing convertibility conditions, used to handle rewriting rules
    that are not left-linear, for example [f &x &x (s &y) → r]. Here, we use a
    condition to test whether the terms at position [{0}] and [{1}] are indeed
    convertible. The rule can only apply if that is the case. Of course we may
    need to check convertibility between more than two terms if a variable has
    more than two occurences. *)
module NLCond : sig
  (** Binary constraint with
      - as {!type:data} a slot of the [vars] array,
      - as {!type:out} a couple of two slots of the [vars] array. *)
  include Cond_sig with
  type exported = int * int and
  type data = int

  (** [constrained i p] tells whether slot [i] is constrained in pool [p]. *)
  val constrained : data -> t -> bool
end = struct
  module IntPairSet = Set.Make(
    struct
      type t = int * int

      let compare : t -> t -> int = fun (i1,i2) (j1,j2) ->
        match i1 - j1 with 0 -> i2 - j2 | k -> k
    end)

  (** A non linearity constraint. *)
  type t =
    { partial : int IntMap.t
    (** An association [(e, v)] is a slot [e] of the [env] array with a slot
        [v] of the [vars] array. *)
    ; available : IntPairSet.t
    (** Pairs of this set are checkable constraints, i.e. the two integers
        refer to available positions in the {!val:vars} array. *) }

  type cond = int * int

  type exported = cond

  type data = int

  let pp_cond oc (i, j) = Format.fprintf oc "(%d,%d)" i j

  let pp oc pool =
    let pp_sep oc _ = Format.pp_print_string oc "; " in
    let pp_int_int oc (i, j) = Format.fprintf oc "@[(%d, %d)@]" i j in
    let pp_partial oc ism =
      Format.fprintf oc "@[partial: %a@]"
        (Format.pp_print_list ~pp_sep pp_int_int) (IntMap.bindings ism)
    in
    let pp_available oc ips =
      Format.fprintf oc "@[available: %a@]"
        (Format.pp_print_list ~pp_sep pp_int_int) (IntPairSet.elements ips)
    in
    Format.fprintf oc "Nl constraints:@,@[<v>%a@,%a@,@]"
      pp_partial pool.partial pp_available pool.available

  let empty = { partial = IntMap.empty ; available = IntPairSet.empty }

  let is_empty c = IntPairSet.is_empty c.available

  let normalize (i, j) = if i < j then (i, j) else (j, i)

  let constrained : data -> t -> bool = fun slot pool ->
    IntMap.mem slot pool.partial

  let is_instantiated pair c = IntPairSet.mem pair c.available

  let remove pair pool =
    { pool with available = IntPairSet.remove pair pool.available }

  let export pair = pair

  let instantiate vslot esl pool =
    try
      let e = normalize (vslot, IntMap.find esl pool.partial) in
      { pool with available = IntPairSet.add e pool.available }
    with Not_found ->
      { pool with partial = IntMap.add esl vslot pool.partial }

  let choose pools =
    let avp = List.map (fun x -> x.available) pools in
    choose IntPairSet.is_empty IntPairSet.choose avp
end

(** Free variable constraints to verify which variables are free in a term. If
    there is a rule of the form [f (λ x y, &Y[y]) → &Y], then we need to check
    that the term at position [{0.0}] depends only on free variable [y]. *)
module FVCond : sig
  (** Binary constraint with
      - as {!type:data} an array of free variables,
      - as {!type:out} the slot of the [vars] array and an array of variables
        that may appear free in the term. *)
  include Cond_sig with
  type exported = int * tvar array and
  type data = tvar array
end = struct
  type t = (tvar array) IntMap.t

  type cond = int * tvar array

  type exported = cond

  type data = tvar array

  let pp_cond oc (sl, vars) =
    let pp_sep oc _ = Format.pp_print_string oc "; " in
    Format.fprintf oc "%d: {@[<h>%a@]}" sl
      (Format.pp_print_list ~pp_sep Print.pp_tvar) (Array.to_list vars)

  let pp oc available =
    let pp_sep oc _ = Format.pp_print_string oc "; " in
    let pp_tvs = Format.pp_print_list ~pp_sep Print.pp_tvar in
    let ppit oc (a, b) =
      Format.fprintf oc "@[(%d, %a)@]" a pp_tvs (Array.to_list b)
    in
    Format.fprintf oc "Fv constraints:@,@[<v>@[available: %a@]@,@]@."
      (Format.pp_print_list ppit) (IntMap.bindings available)

  let empty = IntMap.empty

  let is_empty = IntMap.is_empty

  let is_instantiated (sl, x) p =
    try Array.equal Bindlib.eq_vars x (IntMap.find sl p)
    with Not_found -> false

  let remove (sl, x) p =
    try
      if Array.equal Bindlib.eq_vars x (IntMap.find sl p) then
        IntMap.remove sl p
      else p
    with Not_found -> p

  let instantiate = IntMap.add

  let export x = x

  let choose pools = choose IntMap.is_empty IntMap.choose pools
end

(** {3 Miscellaneous types and definitions} *)

(** Type of the leaves of the tree (see {!field:Terms.rhs}). *)
type action = (term_env, term) Bindlib.mbinder

(** Abstract machine stack. *)
type 'a stack = 'a list

(** {b NOTE} we ideally need the {!type:stack} of terms used during evaluation
    (argument [stk] of {!val:Eval.tree_walk}) to provide fast access to any
    element (for swaps) as well as fast {!val:Extra.List.destruct} and
    {!val:Extra.List.reconstruct} (to inspect a particular element, reduce it,
    and then reinsert it). In practice, the naive representation based on
    lists is faster than more elaborate solutions, unless there are rules with
    {e many} arguments.  Alternatives to a list-based implementation would be
    cat-enable lists / deques, finger trees (Paterson & Hinze) or random
    access lists. In the current implementation, [destruct e i] has a time
    complexity of [Θ(i)] and [reconstruct l m r] has a time complexity of
    [Θ(length l + length m)]. *)

(** {3 Clause matrix and pattern matching problem} *)

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
      as [[0]]. Note that a value [[]] does not describe a valid path. *)

  (** Compile time equivalent of the evaluation time stack of arguments.  The
      [i]th pair [(o, d)] of the stack is the occurrence [o] of type
      {!type:int list} and the number [d] (for depth) of abstractions traversed
      at the [i]th column of th matrix. *)
  type occur_rs = arg list

  (** Data needed to bind terms from the lhs into the rhs. *)
  type binding_data = int * term Bindlib.mvar

  (** A redefinition of the rule type.

      {b Note} that {!type:array} is used while {!type:stack} could
      be used because {!val:pick_best_among} goes through all items of a rule
      anyway ([max(S) = Θ(|S|)]).  Since heuristics need to access elements of
      the matrix, we favour quick access with {!type:array}. *)
  type clause =
    { c_lhs : term array
    (** Left hand side of a rule.   *)
    ; c_rhs : action
    (** Right hand side of a rule. *)
    ; env_builder : (int * binding_data) list
    (** Maps slots of the {!val:vars} array to a slot of the final
        environment used to build the {!field:c_rhs}. *)
    ; nonlin : NLCond.t
    (** Non linearity constraints attached to this rule. *)
    ; freevars : FVCond.t
    (** Free variables constraints attached to the rule. *) }

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
    | Specialise of int
    (** Further specialise the matrix against constructors of a given
        column. *)
    | NlConstrain of NLCond.cond
    (** [NlConstrain(c, s)] indicates a non-linearity constraint on column [c]
        regarding slot [s]. *)
    | FvConstrain of FVCond.cond
    (** Free variables constraint: the term matched must contain {e at most} a
        specified set of variables. *)

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
      { c_lhs = Array.of_list lhs ; c_rhs = rhs ; nonlin = NLCond.empty
      ; freevars = FVCond.empty ; env_builder = [] }
    in
    let size = (* Get length of longest rule *)
      if rs = [] then 0 else
      List.max ~cmp:Int.compare
        (List.map (fun r -> List.length r.Terms.lhs) rs) in
    let positions =
      if size = 0 then []
      else List.init (size - 1) (fun i -> {arg_path = [i]; arg_rank = 0})
    in
    (* [|>] is reverse application, can be thought of as a Unix pipe | *)
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
    switchable |> List.filteri_map switchable2ind |> Array.of_list

  (** [choose m] returns the index of column to switch on. *)
  let choose : t -> int option = fun m ->
    let kept = discard_cons_free m.clauses in
    if kept = [||] then None else
    let sel_partial = pick_best_among m kept in
    Some(kept.(sel_partial))

  (** [is_exhausted p r] returns whether [r] can be applied or not, with [p]
      the occurrences of the terms in [r]. *)
  let is_exhausted : occur_rs -> clause -> bool =
    fun positions {c_lhs = lhs ; nonlin ; freevars ; _} ->
    let nonl lhs =
      (* Verify that there are no non linearity constraints in the remaining
         terms.  We must check that there are no constraints in the remaining
         terms and no constraints left partially instantiated. *)
      let slots = Array.to_list lhs
                 |> List.filter_map
                      (function Patt(io, _, _) -> io | _ -> None) in
      let slots_uniq = List.sort_uniq Int.compare slots in
      List.same_length slots slots_uniq
      && not @@ List.exists (fun s -> NLCond.constrained s nonlin)
        slots_uniq
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
    NLCond.is_empty nonlin && FVCond.is_empty freevars
    && (lhs = [||] || ripe lhs)

  (** [yield m] yields a clause to be applied. *)
  let yield : t -> decision = fun ({ clauses ; positions ; _ } as m) ->
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
      match NLCond.choose @@ List.map (fun r -> r.nonlin) m.clauses with
      | Some(c) -> NlConstrain(c)
      | None    ->
      match FVCond.choose @@ List.map (fun r -> r.freevars) m.clauses with
      | Some(c) -> FvConstrain(c)
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
    List.filter_map keep_treecons telst |> List.sort_uniq tc_fst_cmp

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
        let freevars =
          if (Array.length e) <> a.arg_rank then
            FVCond.instantiate slot (Array.map to_tvar e) r.freevars
          else r.freevars
        in
        let nonlin =
          match i with
          | Some(i) -> NLCond.instantiate slot i r.nonlin
          | None    -> r.nonlin
        in
        let env_builder =
          match i with
          | Some(i) -> (slot, (i, Array.map to_tvar e)) :: r.env_builder
          | None    -> r.env_builder
        in
        { r with env_builder ; nonlin ; freevars }
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

  (** [nl_succeed c r] computes the clause list from [r] that verify a
      non-linearity constraint [c]. *)
  let nl_succeed : NLCond.cond -> clause list -> clause list = fun c ->
    List.map (fun r -> {r with nonlin = NLCond.remove c r.nonlin})

  (** [nl_fail c r] computes the clauses not failing a non-linearity
      constraint [c] among clauses [r]. *)
  let nl_fail : NLCond.cond -> clause list -> clause list = fun c ->
    List.filter (fun r -> not (NLCond.is_instantiated c r.nonlin))

  (** [fv_suceed c r] computes the clauses from [r] that verify a free
      variables constraint [c]. *)
  let fv_succeed : FVCond.cond -> clause list -> clause list = fun c ->
    List.map (fun r -> {r with freevars = FVCond.remove c r.freevars})

  (** [fv_fail c r] computes the clauses not failing a free variable
      constraint [c] among clauses [r]. *)
  let fv_fail : FVCond.cond -> clause list -> clause list = fun c ->
    List.filter (fun r -> not (FVCond.is_instantiated c r.freevars))
end

(** See {!type:Terms.dtree}. *)
type t = (term, action) Tree_types.tree

(** {b Example:} let us consider the rewrite system for symbol [f] defined as:
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

(** [harvest l r e s] exhausts linearly the stack composed only of pattern
    variables with no non linear constraints. *)
let harvest : term array -> action -> (int * CM.binding_data) list -> int ->
  t = fun lhs rhs env_builder slot ->
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
let rec compile : CM.t -> t = fun ({clauses ; positions ; slot} as pats) ->
  if CM.is_empty pats then Fail else
  match CM.yield pats with
  | Yield({c_rhs ; env_builder ; c_lhs ; _}) ->
      if c_lhs = [||] then Leaf(env_builder, c_rhs) else
      harvest c_lhs c_rhs env_builder slot
  | NlConstrain(constr)                      ->
      let ok = compile {pats with clauses = CM.nl_succeed constr clauses} in
      let fail = compile {pats with clauses = CM.nl_fail constr clauses} in
      let (i, j) = NLCond.export constr in
      Cond({ok ; cond = Constr_Eq(i, j) ; fail})
  | FvConstrain(constr)                      ->
      let ok = compile {pats with clauses = CM.fv_succeed constr clauses} in
      let fail = compile {pats with clauses = CM.fv_fail constr clauses} in
      let (slot, vars) = FVCond.export constr in
      Cond({ok ; cond = Constr_FV(vars, slot) ; fail})
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
