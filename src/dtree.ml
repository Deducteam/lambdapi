(** This module provides functions to compile rewrite rules to decision trees
    in order to pattern match the rules efficiently.  The method is based on
    Luc Maranget's {i Compiling Pattern Matching to Good Decision Trees},
    {{:10.1145/1411304.1411311}DOI}. *)
open Terms
open Extra
open Basics
open Treecons

(** See {!type:tree} in {!module:Terms}. *)
type t = tree

(** Type of the leaves of the tree.  See {!module:Terms}, {!field:rhs}. *)
type action = (term_env, term) Bindlib.mbinder

(** An exception raised if trying to match an abstraction. *)
exception Not_implemented

(** {b Example} Given a rewrite system for a symbol [f] given as
    - [f Z (S m)     → S m]
    - [f n Z         → n]
    - [f (S n) (S m) → S (S m)]

    A possible tree might be
    {v
    +–?–∘–Z–∘     → n
    ├–Z–∘–Z–∘     → n
    |   └–S–∘–?–∘ → S m
    └–S–∘–Z–∘     → n
    └–S–∘–?–∘     → S (S m)
    v}
    with [∘] being a node (with a label not shown here) and [–u–]
    being an edge with a matching on symbol [u] or a variable or wildcard when
    [?].  Typically, the portion [S–∘–Z] is made possible by a swap. *)

(** {3 Reduction substrate} *)

(** Data structure used when reducing terms. When reducing, we must have
    - fast access to any element in the substrate: for swaps
    - fast split and merge: to remove an element (the inspected one), reduce
      it, or unfold it (if an {!constructor:Appl} node) and then reinsert
      it.
    Otherwise, it behaves like a stack. *)
module type Reduction_substrate =
sig
  (** Type of a substrate of ['a]. *)
  type 'a t

  (** The empty substrate. *)
  val empty : 'a t

  (** [is_empty v] returns whether a substrate is empty. *)
  val is_empty : 'a t -> bool

  (** [of_list l] returns a substrate containing the elements of [l]. *)
  val of_list : 'a list -> 'a t

  (** [to_list s] returns a list containing the elements of the substrate
      [s]. *)
  val to_list : 'a t -> 'a list

  (** [length v] is the number of elements in [v]. *)
  val length : 'a t -> int

  type 'a prefix
  type 'a suffix
  (** Prefix and suffix of the substrate. *)

  (** [destruct v i] returns a triplet [(l, m, r)] with [l]eft being the
      elements from 0 to [i - 1], [m]iddle the [i]th element and [r]ight the
      elements from [i + 1] to the end of [v].
      @raise invalid_arg when [i < 0]
      @raise Not_found when [i ≥ length v]. *)
  val destruct : 'a t -> int -> 'a prefix * 'a * 'a suffix

  (** [restruct l m r] is the concatenation of three substrates [l] [m] and
      [r]. *)
  val restruct : 'a prefix -> 'a list -> 'a suffix -> 'a t

  (** [of_seq s] returns a list containing elements of sequence [s]. *)
  val of_seq : 'a Seq.t -> 'a t

  (** [to_seq s] converts substrate [s] to a sequence. *)
  val to_seq : 'a t -> 'a Seq.t
end

(** Naive implementation based on lists.  Appeared to be faster than tree
    based structures (except when having rules with {e a lot} of
    arguments). *)
module RedListStack : Reduction_substrate =
struct
  type 'a t = 'a list
  type 'a prefix = 'a list
  type 'a suffix = 'a list
  let empty = []
  let is_empty l = (=) [] l
  let of_list l = l
  let to_list s = s

  (** [length l] complexity in [Θ(length l)]. *)
  let length = List.length

  (** [destruct e i] complexity in [Θ(i)]. *)
  let destruct e i =
    if i < 0 then invalid_arg "RedListStack.destruct" ;
    let rec destruct l i r =
      match (r, i) with
      | ([]  , _) -> raise Not_found
      | (v::r, 0) -> (l, v, r)
      | (v::r, i) -> destruct (v :: l) (i - 1) r
    in
    destruct [] i e

  (** [restruct l c r] complexity in [Θ(length (l @ c))]*)
  let restruct l c r =
    let rec insert acc l =
      match l with
      | []   -> acc
      | x::l -> insert (x :: acc) l
    in
    insert (c @ r) l

  let of_seq = List.of_seq
  let to_seq = List.to_seq
end

module ReductionStack = RedListStack

(** {3 Graphviz output} *)

(** Printing hint for conversion to graphviz. *)
type dot_term =
  | DotDefa
  | DotAbst of tvar
  | DotCons of treecons

(** [to_dot f t] creates a dot graphviz file [f].gv for tree [t].  Each node
    of the tree embodies a pattern matrix.  The label of a node is the
    column index in the matrix on which the matching is performed to give
    birth to children nodes.  The label on the edge between a node and one of
    its children represents the term matched to generate the next pattern
    matrix (the one of the child node); and is therefore one of the terms in
    the column of the pattern matrix whose index is the label of the node. *)
let to_dot : string -> t -> unit = fun fname tree ->
  let module F = Format in
  let module P = Print in
  let ochan = open_out (fname ^ ".gv") in
  let ppf = F.formatter_of_out_channel ochan in
  let nodecount = ref 0 in
  F.fprintf ppf "graph {@[<v>" ;
  let pp_dotterm : dot_term pp = fun oc dh -> match dh with
    | DotAbst(v) -> F.fprintf oc "λ%a" Print.pp_tvar v
    | DotDefa    -> F.fprintf oc "*"
    | DotCons(TcSymb(t)) -> F.fprintf oc "%s<sub>%d</sub>" t.c_sym t.c_ari
    | DotCons(TcVari(s)) -> F.fprintf oc "%s" s
    | DotCons(TcAbst)    -> assert false in
  let pp_tcstr : tree_constraint pp = fun oc -> function
    | TcstrEq(i, j)    -> F.fprintf oc "@%d≡<sub>v</sub>@%d" i j
    | TcstrFreeVars(_) -> raise Not_implemented in
  (* [write_tree n u v] writes tree [v] obtained from tree number [n] with a
     switch on [u] ({!constructor:None} if default). *)
  let rec write_tree : int -> dot_term -> t -> unit = fun father_l swon ->
    function
    | Leaf(_, a)       ->
        incr nodecount ;
        let _, acte = Bindlib.unmbind a in
        F.fprintf ppf "@ %d [label=\"%a\"];" !nodecount P.pp acte ;
        F.fprintf ppf "@ %d -- %d [label=<%a>];"
          father_l !nodecount pp_dotterm swon
    | Node(ndata)      ->
        let { swap ; children ; store ; abstraction ; default } = ndata in
        incr nodecount ;
        let tag = !nodecount in
        (* Create node *)
        F.fprintf ppf "@ %d [label=\"@%d\"%s];"
          tag swap (if store then " shape=\"box\"" else "") ;
        (* Create edge *)
        F.fprintf ppf "@ %d -- %d [label=<%a>];"
          father_l tag pp_dotterm swon ;
        TcMap.iter (fun s e -> write_tree tag (DotCons(s)) e) children ;
        Option.iter (fun (v, t) -> write_tree tag (DotAbst(v)) t) abstraction ;
        Option.iter (write_tree tag DotDefa) default ;
    | Condition(cdata) ->
        let { ok ; condition ; fail } = cdata in
        incr nodecount ;
        let tag = !nodecount in
        F.fprintf ppf "@ %d [label=<%a> shape=\"diamond\"];"
          tag pp_tcstr condition ;
        F.fprintf ppf "@ %d -- %d [label=<%a>];"
          father_l tag pp_dotterm swon ;
        write_tree tag DotDefa ok ;
        write_tree tag DotDefa fail ;
    | Fail             ->
        incr nodecount ;
        F.fprintf ppf "@ %d [label=<!>];" !nodecount ;
        F.fprintf ppf "@ %d -- %d [label=\"!\"];" father_l !nodecount in
  begin match tree with
  (* First step must be done to avoid drawing a top node. *)
  | Node({ swap ; store ; children ;
           default ; abstraction }) ->
      F.fprintf ppf "@ 0 [label=\"@%d\"%s];"
        swap (if store then " shape=\"box\"" else "") ;
      TcMap.iter (fun sw c -> write_tree 0 (DotCons(sw)) c) children ;
      Option.iter (fun (v, t) -> write_tree 0 (DotAbst(v)) t) abstraction ;
      Option.iter (fun t -> write_tree 0 DotDefa t) default
  | Leaf(_)                         -> ()
  | _                               -> assert false
  end ;
  F.fprintf ppf "@.}@\n@?" ;
  close_out ochan

(** {3 Binary constraints nodes} *)

(** Binary constraints allow to check properties on terms during evaluation.
    A constraint is binary as it gives birth to two trees, one used if the
    constraint is satisfied and the other used if not.

    Currently, binary constraints are used
    - to check non linear constraints in the left hand side of a rule (e.g. in
      presence of the rule like [f &X &X (s &Y) → &Y]).  In this case, the
      constraint node created will force the rewriting engine to verify that
      the terms at position [{0}] and [{1}] are convertible.
    - to verify which variables are free in a term.  If there is a rule of the
      form [f &X[x, y] &Y[y] → &Y], then the rewriting engine must verify that
      the term at position [{0}] depends only on free variables [x] and [y] and
      that the term at position [{1}] depends only on free variable [y].

    Constraints depends heavily on the {!val:vars} array used to store terms
    during evaluation as it is the only way to have access to terms matched
    while evaluating.  The term {i slot} refers to a position in this array.
    The slot is determined via the {!field:slot} which is incremented each
    time a {!constructor:Patt} is encountered. *)

(** A general type for a pool of constraints.  Constraints are first parsed
    from lhs and stored using their position.  At the beginning, constraints
    are not available for checking, as at the beginning of evaluation, the
    terms are not yet known.  During tree build, a constraint is {e
    instantiated} if the position to which it refers is inspected (chosen for
    specialisation).  When a constraint is fully instantiated, it is marked as
    available which means that the rewriting engine is able to verify the
    constraint (because the concerned terms from the term stack have been
    parsed). *)
module type BinConstraintPoolSig =
sig
  (** Set of constraints declared, either available or not. *)
  type t

  (** A unique instantiated constraint. *)
  type cstr

  (** Action to perform. *)
  type decision =
    | Solve of cstr * int
    (** A constraint to apply along with its heuristic score. *)
    | Instantiate of Subterm.t * int
    (** Carry out a switch on a term specified by its position.  A switch can
        be performed to expose a pattern variable having a constraint.  The
        [int] is the heuristic score. *)
    | Unavailable
    (** No constraint available. *)

  (** [pp_cstr o c] prints constraint [c] to channel [o]. *)
  val pp_cstr : cstr pp

  (** [pp o p] prints pool [p] to channel [o]. *)
  val pp : t pp

  (** The empty set of constraints. *)
  val empty : t

  (** [is_empty p] returns whether pool [p] is empty. *)
  val is_empty : t -> bool

  (** [concerns p q] returns true if position [p] hasn't been instantiated yet
      in pool [q] and if [p] is involved in a constraint. *)
  val concerns : Subterm.t -> t -> bool

  (** [is_instantiated c p] returns whether pool [p] has constraint [c]
      instantiated. *)
  val is_instantiated : cstr -> t -> bool

  (** [remove c p] removes constraint [c] from pool [p]. *)
  val remove : cstr -> t -> t

  (** [instantiate p i q] instantiates path [p] in pool [q] using index [i],
      that is, mark a path as {i seen} in the constraints.  Typically, if a
      constraint involves only one variable, then instantiating a variable is
      equivalent to instantiating a constraint.  However, if a constraint
      involves several variables, then instantiating a variable will promote
      the constraint to a {e partially instantiated state}, and will be
      completely instantiated when all the variables are instantiated.
      @raise Not_found if [p] is not part of any constraint in [q]. *)
  val instantiate : Subterm.t -> int -> t -> t

  (** [choose p] returns the best action to perform considering a list of
      constraints [p]. *)
  val choose : t list -> decision

  (** [of_terms r] returns constraint pool induced by terms in [r]. *)
  val of_terms : term list -> t

  (** [export c] returns the data needed for evaluation from a constraint
      [c].  The return type is to be defined by the implementations. *)
  val export : cstr -> 'a
end

(** Non linearity constraints signature.  A non linearity constraint involves
    at least two variables. *)
module type NlConstraintSig =
sig
  include BinConstraintPoolSig

  (** [export c] returns the two slots containing the terms that must be
      convertible. *)
  val export : cstr -> int * int
end

(** Free variables constraints.  Such a constraint involves only one variable,
    but it requires the list of variables that may appear free in the term. *)
module type FvConstraintSig =
sig
  include BinConstraintPoolSig

  (** [export c] returns the slot of a term along with the free variables that
      might appear free in it. *)
  val export : cstr -> int * tvar list

end

module NlConstraints : NlConstraintSig =
struct

  module IntPair =
  struct
    type t = int * int
    let compare : t -> t -> int = fun (i, i') (j, j') ->
      match Int.compare i j with
      | 0 -> Int.compare i' j'
      | k -> k
  end

  module IntPairSet = Set.Make(IntPair)
  module IntPairMap = Map.Make(IntPair)

  type t =
    { concerned : SubtSet.t
    (** All the positions concerned by non linear constraints. *)
    ; groups : (int * SubtSet.t) list
    (** Set of path that are still subject to non linearity constraints.  An
        element [(i, C)] is a slot [i] along with all the positions of the
        variables sharing this slot. *)
    ; partial : int SubtMap.t
    (** A tuple [(p, h)] of this mapping indicates that path [p] in the
        arguments has a non linearity constraint with term store at position
        [h] of the {!val:vars} array. *)
    ; available : IntPairSet.t
    (** Pairs of this set are checkable constraints, i.e. the two integers
        refer to available positions in the {!val:vars} array. *) }

  type cstr = int * int

  type decision = Solve of cstr * int
                | Instantiate of Subterm.t * int
                | Unavailable

  let pp_cstr oc (i, j) = Format.fprintf oc "(%d,%d)" i j

  let pp oc pool =
    let module F = Format in
    let pp_subtset oc ss =
      F.fprintf oc "@[{%a}@]"
        (F.pp_print_list
           ~pp_sep:(fun oc () -> F.pp_print_string oc ";")
           Subterm.pp)
        (SubtSet.elements ss) in
    let pp_int_subtset oc (i, ss) =
      F.fprintf oc "@[(%d, %a)@]" i pp_subtset ss in
    let pp_groups oc pgroups =
      F.fprintf oc "@[groups: @[<v 2>%a@]@]"
        (F.pp_print_list
           ~pp_sep:(F.pp_print_cut)
           pp_int_subtset)
        pgroups in
    let pp_subterm_int oc (st, i) =
      F.fprintf oc "@[(%a, %d)@]" Subterm.pp st i in
    let pp_partial oc ism =
      F.fprintf oc "@[partial: %a@]"
        (F.pp_print_list
           ~pp_sep:(fun oc () -> F.pp_print_string oc ";")
           pp_subterm_int)
        (SubtMap.bindings ism) in
    let pp_int_int oc (i, j) = F.fprintf oc "@[(%d, %d)@]" i j in
    let pp_available oc ips =
      F.fprintf oc "@[available: %a@]"
        (F.pp_print_list
           ~pp_sep:(fun oc () -> F.pp_print_string oc ";")
           pp_int_int)
        (IntPairSet.elements ips) in
    F.fprintf oc "Nl constraints:@," ;
    F.fprintf oc "@[<v>" ;
    F.fprintf oc "%a@," pp_groups pool.groups ;
    F.fprintf oc "%a@," pp_partial pool.partial ;
    F.fprintf oc "%a@," pp_available pool.available ;
    F.fprintf oc "@]"

  let empty = { concerned = SubtSet.empty
              ; groups = []
              ; partial = SubtMap.empty
              ; available = IntPairSet.empty }

  let is_empty { groups ; partial ; available ; concerned = _ } =
    groups = empty.groups && partial = empty.partial &&
    available = empty.available

  let normalize (i, j) = if Int.compare i j < 0 then (i, j) else (j, i)

  let choose cstrs =
    if List.for_all is_empty cstrs then Unavailable else
    let available = List.fold_right (fun c -> IntPairSet.union c.available)
        cstrs IntPairSet.empty in
    match IntPairSet.choose_opt available with
    | Some(c) -> Solve(c, 1)
    | None    ->
        let positions = List.fold_right
            (fun c -> c.partial |> SubtMap.bindings |> List.map fst |> (@))
            cstrs [] |> List.sort_uniq Subterm.compare in
        match positions with
        | x :: _ -> Instantiate(x, 1)
        | []     ->
            let g2s sl2po = List.fold_right (fun (_, ps) -> SubtSet.union ps)
                sl2po SubtSet.empty in
            let positions = List.fold_right
                (fun c -> c.groups |> g2s |> SubtSet.union)
                cstrs SubtSet.empty in
            let p = SubtSet.choose positions in
            Instantiate(p, 1)

  let is_instantiated pair { available ; _ } = IntPairSet.mem pair available

  let concerns p q = SubtSet.mem p q.concerned

  let remove pair pool = { pool with
                           available = IntPairSet.remove pair pool.available }

  let export pair = pair

  let instantiate path i pool =
    match SubtMap.find_opt path pool.partial with
    | Some(j) ->
        let npartial = SubtMap.remove path pool.partial in
        let navailable = IntPairSet.add (normalize (i, j)) pool.available in
        { pool with partial = npartial ; available = navailable }
    | None    ->
        let (k, set) = List.find
            (fun (_, s) -> SubtSet.mem path s)
            pool.groups in
        let ngroups = List.remove_assoc k pool.groups in
        (* Don't put the examined position in partial *)
        let set = SubtSet.remove path set in
        let npartial = SubtSet.fold (fun pth -> SubtMap.add pth i) set
            pool.partial in
        { pool with partial = npartial ; groups = ngroups }

  (** [of_terms r] returns the non linearity set of constraints associated to
      list of terms [r]. *)
  let of_terms r =
    (* [groupby_slot r] returns an associative list mapping final environment
       slot to subterm position in [r]. *)
    let groupby_slot: term list -> (int * SubtSet.t) list = fun lhs ->
      let add po io _ _ acc =
        match io with
        | None     -> acc
        | Some(sl) ->
            List.modify_opt sl
              (function None      -> SubtSet.singleton po
                      | Some(set) -> SubtSet.add po set)
              acc in
      let merge ala alb = List.assoc_merge SubtSet.union SubtSet.empty
          (ala @ alb) in
      fold_vars lhs ~add:add ~merge:merge ~init:[] in
    let nlcons = groupby_slot r |>
                 List.filter (fun (_, s) -> SubtSet.cardinal s > 1) in
    let everyone = List.fold_right
        (fun (_, v) -> SubtSet.union v) nlcons SubtSet.empty in
    { groups = nlcons ; partial = SubtMap.empty ; available = IntPairSet.empty
    ; concerned = everyone }
end

module FvConstraints : FvConstraintSig =
struct
  type t = { involved : (tvar list) SubtMap.t
           ; available : (tvar list) IntMap.t }

  type cstr = int * tvar list

  type decision = Solve of cstr * int
                | Instantiate of Subterm.t * int
                | Unavailable

  let pp_cstr oc (sl, vars) =
    let module F = Format in
    Format.fprintf oc "%d: {@[<h>%a@]}" sl
      (Format.pp_print_list
         ~pp_sep:(fun oc () -> Format.pp_print_string oc "; ") Print.pp_tvar)
      vars

  let pp oc { available ; involved } =
    let module F = Format in
    let pp_tvs : tvar list pp = F.pp_print_list
        ~pp_sep:(fun oc () -> F.fprintf oc "; ")
        Print.pp_tvar in
    let ppst : (Subterm.t * tvar list) pp = fun oc (a, b) ->
      F.fprintf oc "@[(%a, %a)@]" Subterm.pp a pp_tvs b in
    let ppit : (int * tvar list) pp = fun oc (a, b) ->
      F.fprintf oc "@[(%d, %a)@]" a pp_tvs b in
    F.fprintf oc "Fv constraints:@," ;
    F.fprintf oc "@[<v>" ;
    F.fprintf oc "@[involved: %a@]@,"
      (F.pp_print_list ppst)
      (SubtMap.bindings involved) ;
    F.fprintf oc "@[available: %a@]@,"
      (F.pp_print_list ppit)
      (IntMap.bindings available) ;
    F.fprintf oc "@]@."

  let empty = { involved = SubtMap.empty ; available = IntMap.empty }

  let is_empty p = p.involved = empty.involved && p.available = empty.available

  let concerns s p = SubtMap.mem s p.involved

  let is_instantiated (sl, _) p = IntMap.mem sl p.available

  let remove (sl, _) p = { p with available = IntMap.remove sl p.available }

  let instantiate s sl p =
    let vars = SubtMap.find s p.involved in
    { involved = SubtMap.remove s p.involved
    ; available = IntMap.add sl vars p.available }

  let export x = x

  let of_terms tes =
    let add po _ _ e acc =
      if e = [||] then acc else
      let vars = Array.to_seq e |> Seq.map to_tvar |> List.of_seq in
      SubtMap.add po vars acc in
    let merge = SubtMap.union (fun _ _ _ -> assert false) in
    let involved = fold_vars tes ~add:add ~merge:merge ~init:SubtMap.empty in
    { empty with involved }

  let rec choose = fun cs ->
    let r = match cs with
    | []      -> Unavailable
    | p :: ps ->
    match IntMap.choose_opt p.available with
    | None       -> choose ps
    | Some(i, x) -> Solve((i, x), 1) in
    if r <> Unavailable then r else
    match cs with
    | []    -> Unavailable
    | p::ps ->
    match SubtMap.choose_opt p.involved with
    | None         -> choose ps
    | Some(sub, _) -> Instantiate(sub, 1)

end

(** A helper type to process [choose] results uniformly. *)
type bin_cstr = Fv of FvConstraints.cstr
              | Nl of NlConstraints.cstr
              | Instantiate of Subterm.t
              | Sp of int
              | Unavailable

(** {3 Clause matrix and pattern matching problem} *)

(** A clause matrix encodes a pattern matching problem.  The clause matrix {i
    C} can be denoted {i C = P → A} where {i P} is a {e pattern matrix} and {i
    A} is a column of {e actions}.  Each line of a pattern matrix is a pattern
    to which is attached an action.  When reducing a term, if a line filters
    the term, or equivalently the term matches the pattern, the term is
    rewritten to the action. *)
module ClauseMat =
struct

  (** For convenience. *)
  type subt_rs = Subterm.t ReductionStack.t

  (** A redefinition of the rule type.

      {b Note} that {!type:array} is used while {!module:ReductionStack} could
      be used because {!val:pick_best_among} goes through all items of a rule
      anyway ([max(S) = Θ(|S|)]).  Since heuristics need to access elements of
      the matrix, we favour quick access with {!type:array}. *)
  type rule =
    { lhs : term array
    (** Left hand side of a rule.   *)
    ; rhs : action
    (** Right hand side of a rule. *)
    ; env_builder : (int * int) list
    (** Maps slots of the {!val:vars} array to a slot of the final
        environment used to build the {!field:rhs}. *)
    ; nonlin : NlConstraints.t
    (** Non linearity constraints attached to this rule. *)
    ; freevars : FvConstraints.t
    (** Free variables constraints attached to the rule. *) }

  (** Type of a matrix of patterns.  Each line is a row having an attached
      action. *)
  type t =
    { clauses : rule list
    (** The rules. *)
    ; slot : int
    (** Index of next slot to use in {!val:vars} array to store variables. *)
    ; positions : subt_rs
    (** Positions of the elements of the matrix in the initial term.  We rely
        on the order relation used in sets. *) }

  (** Operations embedded in the tree *)
  type decision =
    | Yield of rule
    (** Apply a rule. *)
    | Specialise of int
    (** Further specialise the matrix against constructors of a given
        column. *)
    | NlConstrain of NlConstraints.cstr
    (** [NlConstrain(c, s)] indicates a non-linearity constraint on column [c]
        regarding slot [s]. *)
    | FvConstrain of FvConstraints.cstr
    (** Free variables constraint: the term matched must contain {e at most} a
        specified set of variables. *)

  (** [pp o m] prints matrix [m] to out channel [o]. *)
  let pp : t pp = fun oc { clauses ; positions ; _ } ->
    let module F = Format in
    let pp_line oc l =
      F.fprintf oc "@[<h>" ;
      F.pp_print_list ~pp_sep:(fun _ () -> F.fprintf oc ";@ ")
        Print.pp oc (Array.to_list l) ;
      F.fprintf oc "@]" in
    F.fprintf oc "Positions @@ @[<h>" ;
    F.pp_print_list ~pp_sep:(fun oc () -> F.fprintf oc ";") Subterm.pp oc
      (ReductionStack.to_list positions) ;
    F.fprintf oc "@]@," ;
    F.fprintf oc "{@[<v>@," ;
    F.pp_print_list ~pp_sep:F.pp_print_cut pp_line oc
      (List.map (fun { lhs ; _ } -> lhs) clauses) ;
    F.fprintf oc "@.}@,"

  (** [of_rules r] creates the initial pattern matrix from a list of rewriting
      rules. *)
  let of_rules : Terms.rule list -> t = fun rs ->
    let r2r r =
      let lhs = Array.of_list r.Terms.lhs in
      let nonlin = NlConstraints.of_terms r.lhs in
      let freevars = FvConstraints.of_terms r.lhs in
      { lhs ; rhs = r.Terms.rhs ; nonlin ; freevars ; env_builder = [] } in
    let positions = match rs with
      | []   -> ReductionStack.empty
      | r::_ ->
          Subterm.sequence (List.length r.lhs) |>
          ReductionStack.of_seq in
    { clauses = List.map r2r rs ; slot = 0 ; positions }

  (** [is_empty m] returns whether matrix [m] is empty. *)
  let is_empty : t -> bool = fun m -> m.clauses = []

  (** [get_col n m] retrieves column [n] of matrix [m]. *)
  let get_col : int -> t -> term list = fun ind { clauses ; _ } ->
    List.map (fun { lhs ; _ } -> lhs.(ind)) clauses

  (** [score c] returns the score heuristic for column [c]. *)
  let rec score : term list -> int = function
    | []                         -> 0
    | x :: xs when is_treecons x -> score xs
    | _ :: xs                    -> succ (score xs)

  (** [pick_best_among m c] returns the index of the best column of matrix [m]
      among columns [c] according to a heuristic, along with the score. *)
  let pick_best_among : t -> int array -> int * int = fun mat columns->
    let wild_pc = Array.map (fun ci ->
      let c = get_col ci mat in score c) columns in
    let index = Array.argmax (<=) wild_pc in
    (index, wild_pc.(index))

  (** [can_switch_on r k] returns whether a switch can be carried out on
      column [k] of rules [r]. *)
  let can_switch_on : rule list -> int -> bool = fun  clauses k ->
    let rec loop : rule list -> bool = function
      | []      -> false
      | r :: rs -> if is_treecons r.lhs.(k) then true else loop rs in
    loop clauses

  (** [discard_cons_free r] returns the list of indexes of columns containing
      terms that can be matched against (discard constructor-free columns) in
      rules [r]. *)
  let discard_cons_free : rule list -> int array = fun clauses ->
    let ncols = List.extremum (>)
      (List.map (fun { lhs ; _ } -> Array.length lhs) clauses) in
    let switchable = List.init ncols (can_switch_on clauses) in
    let switchable2ind i e = if e then Some(i) else None in
    switchable |> List.filteri_map switchable2ind |> Array.of_list

  (** [choose m] returns the index of column to switch on. *)
  let choose : t -> (int * int) option = fun m ->
    let kept = discard_cons_free m.clauses in
    if kept = [||] then None else
    let sel_partial, score = pick_best_among m kept in
    let cind = kept.(sel_partial) in
    Some(cind, score)

  (** [is_exhausted r] returns whether [r] can be applied or not. *)
  let is_exhausted : rule -> bool = fun { lhs ; nonlin ; freevars ; _ } ->
    Array.for_all (fun e -> not (is_treecons e)) lhs &&
    NlConstraints.is_empty nonlin &&
    FvConstraints.is_empty freevars

  (** [yield m] yields a rule to be applied. *)
  let yield : t -> decision = fun m ->
    let { clauses ; positions ; _ } = m in
    match List.find_opt is_exhausted clauses with
    | Some(r) -> Yield(r)
    | None    ->
        (* All below could be simplified using either a functor or gadt. *)
        let nlcstrs = List.map (fun r -> r.nonlin) m.clauses in
        let rnl = match NlConstraints.choose nlcstrs with
          | NlConstraints.Solve(c, i)       -> (Nl(c), i)
          | NlConstraints.Instantiate(s, i) -> (Instantiate(s), i)
          | NlConstraints.Unavailable       -> (Unavailable, min_int) in
        let fvcstrs = List.map (fun r -> r.freevars) m.clauses in
        List.iter (fun r -> FvConstraints.pp Format.std_formatter r.freevars)
          m.clauses ;
        let rfv = match FvConstraints.choose fvcstrs with
          | FvConstraints.Solve(c, i)       -> (Fv(c), i)
          | FvConstraints.Instantiate(s, i) -> (Instantiate(s), i)
          | FvConstraints.Unavailable       -> (Unavailable, min_int) in
        let rs = match choose m with
          | None       -> (Unavailable, min_int)
          | Some(c, i) -> (Sp(c), i) in
        let r = [| rnl ; rfv ; rs |] in
        let best =
          if Array.for_all (fun (x, _) -> x = Unavailable) r
          then (Unavailable, min_int)
          else Array.max (fun (_, x) (_, y) -> x >= y) r in
        match fst best with
        | Nl(c)          -> NlConstrain(c)
        | Fv(c)          -> FvConstrain(c)
        | Sp(c)          -> Specialise(c)
        | Instantiate(p) ->
            let ls_rs = ReductionStack.to_seq positions |> List.of_seq in
            let plcp = Subterm.lcp p ls_rs in
            let col = Array.search (fun x -> Subterm.compare x plcp)
                        (Array.of_list ls_rs) in
            Specialise(col)
        | Unavailable    -> assert false

  (** [get_cons l] extracts, sorts and uniqify terms that are tree
      constructors in [l].  The actual tree constructor (of type
      {!type:treecons}) is returned along the original term. *)
  let get_cons : term list -> (treecons * term) list = fun telst ->
    let keep_treecons e =
      if is_treecons e then Some(treecons_of_term e, e) else None in
    let tc_fst_cmp (tca, _) (tcb, _) = tc_compare tca tcb in
    telst |> List.filter_map keep_treecons |> List.sort_uniq tc_fst_cmp

  (** [store m c] returns whether the inspected term on column [c] of matrix
      [m] needs to be stored during evaluation*)
  let store : t -> int -> bool = fun cm ci ->
    let _, pos, _ = ReductionStack.destruct cm.positions ci in
    let st_r r =
      FvConstraints.concerns pos r.freevars ||
      (match r.lhs.(ci) with Patt(Some(_), _, _) -> true | _ -> false) in
    List.exists st_r cm.clauses

  (** [update_aux c p v r] returns rule [r] with auxiliary data updated
      (i.e. non linearity constraints and environment builder) when inspecting
      column [c] having argument at position [p] and having met [v] vars until
      now. *)
  let update_aux : int -> Subterm.t -> int -> rule -> rule =
    fun ci pos slot r ->
    let t = r.lhs.(ci) in
    match fst (get_args t) with
    | Patt(Some(i), _, _) ->
        let env_builder = (slot, i) :: r.env_builder in
        let nonlin = if NlConstraints.concerns pos r.nonlin
          then NlConstraints.instantiate pos slot r.nonlin
          else r.nonlin in
        let freevars = if FvConstraints.concerns pos r.freevars
          then FvConstraints.instantiate pos slot r.freevars
          else r.freevars in
        { r with env_builder ; nonlin ; freevars }
    | _                   -> r

  (** [specialize p c s r] specializes the rules [r] when matching pattern [p]
      against column [c] with positions [s].  A matrix can be specialized by a
      user defined symbol.  In case an {!constructor:Appl} is given as pattern
      [p], only terms having the same number of arguments and the same
      leftmost {e non} {!constructor:Appl} term match. *)
  let specialize : term -> int -> subt_rs -> rule list ->
    subt_rs * rule list = fun pat ci pos rs ->
    let pos =
      let l, m, r = ReductionStack.destruct pos ci in
      let nargs = get_args pat |> snd |> List.length in
      let replace = Subterm.sequence ~from:(Subterm.sub m) nargs in
      ReductionStack.restruct l (List.of_seq replace) r in
    let ph, pargs = get_args pat in
    let insert r e = Array.concat [ Array.sub r.lhs 0 ci
                                  ; e
                                  ; Array.drop (ci + 1) r.lhs ] in
    let filtrans r =
      let insert = insert r in
      let h, args = get_args r.lhs.(ci) in
      match ph, h with
      | Symb(_, _), Symb(_, _)
      | Vari(_)   , Vari(_)       ->
          if List.same_length args pargs && eq ph h
          then Some({r with lhs = insert (Array.of_list args)})
          else None
      | _         , Patt(_, _, _) ->
          let arity = List.length pargs in
          let e = Array.make arity (Patt(None, "", [||])) in
          Some({ r with lhs = insert e })
      | _         , Abst(_, _)    -> None
      | _         , _             -> assert false in
    (pos, List.filter_map filtrans rs)

  (** [default c s r] computes the default rules from [r] that remain to be
      matched in case the pattern used is not in the column [c]. [s] is the
      list of positions of the elements in each rule. *)
  let default : int -> subt_rs -> rule list -> subt_rs * rule list =
    fun ci pos rs ->
    let pos =
      let l, _, r = ReductionStack.destruct pos ci in
      ReductionStack.restruct l [] r in
    let transf r =
      match r.lhs.(ci) with
      | Patt(_, _, _)           ->
          let lhs = Array.append
              (Array.sub r.lhs 0 ci)
              (Array.drop (ci + 1) r.lhs) in
          Some({ r with lhs })
      | Symb(_, _) | Abst(_, _)
      | Vari(_)    | Appl(_, _) -> None
      | _ -> assert false in
    (pos, List.filter_map transf rs)

  (** [abstract c v p r] computes the rules resulting from the specialisation
      by an abstraction.  Note that the pattern can't be an applied lambda
      since the lhs is in normal form. *)
  let abstract : int -> tvar -> subt_rs -> rule list -> subt_rs * rule list =
    fun ci v pos rules ->
    let l, p, r = ReductionStack.destruct pos ci in
    let p = Subterm.sub p in (* Position of term inside lambda. *)
    let pos = ReductionStack.restruct l [p] r in
    let insert r e = [ Array.sub r.lhs 0 ci
                     ; [| e |]
                     ; Array.drop (ci + 1) r.lhs ] in
    let transf (r:rule) =
      match r.lhs.(ci) with
      | Abst(_, b)     ->
          let b = Bindlib.subst b (mkfree v) in
          let lhs = Array.concat (insert r b) in
          Some({ r with lhs })
      | Patt(io, n, e) ->
          let env = Array.append e [| mkfree v |] in
          let lhs = Array.concat (insert r (Patt(io, n, env))) in
          Some({ r with lhs })
      | Symb(_, _)
      | Vari(_)        -> None
      | _              -> assert false in
    (pos, List.filter_map transf rules)

  (** [nl_succeed c r] computes the rule list from [r] that verify a
      non-linearity constraint [c]. *)
  let nl_succeed : NlConstraints.cstr -> rule list -> rule list = fun c ->
    let f r =
      let nonlin = NlConstraints.remove c r.nonlin in
      { r with nonlin } in
    List.map f

  (** [nl_fail c r] computes the rules not failing a non-linearity constraint
      [c] among rules [r]. *)
  let nl_fail : NlConstraints.cstr -> rule list -> rule list = fun c ->
    let f { nonlin ; _ } = not (NlConstraints.is_instantiated c nonlin) in
    List.filter f

  (** [fv_suceed c r] computes the rules from [r] that verify a free variables
      constraint [c]. *)
  let fv_succeed : FvConstraints.cstr -> rule list -> rule list = fun c ->
    let f r =
      let freevars = FvConstraints.remove c r.freevars in
      { r with freevars } in
    List.map f

  (** [fv_fail c r] computes the rules not failing a free variable constraint
  [c] among rules [r]. *)
  let fv_fail : FvConstraints.cstr -> rule list -> rule list = fun c ->
    let f { freevars ; _ } = not (FvConstraints.is_instantiated c freevars) in
    List.filter f
end

module Cm = ClauseMat

(** {b Note} The compiling step creates a tree ready to be used for pattern
    matching.  A tree guides the pattern matching by
    - accepting constructors and filtering possible rules,
    - guiding the matching in order to carry out as few atomic matchings as
      possible by selecting the most appropriate term in the stack,
    - storing terms from the stack that might be used in the right hand side,
      because they match a pattern variable {!constructor:Patt} in the
      {!field:lhs}.

    The first bullet is ensured using {!val:specialize}, {!val:default} and
    {!val:abstract} which allow to create new branches.

    Efficiency is managed thanks to heuristics handled by the {!val:score}
    function.

    The last is managed by the {!val:env_builder} as follows.
    The evaluation process uses, along with the tree, an array [vars] to store
    terms matched against a pattern variable which is used in some
    {!field:rhs}.  Each rule has an {!val:env_builder} mapping a index in the
    [vars] array to a slot in the final environment (the slot [i] of a
    [Patt(Some(i), _, _)]).  Note that the [vars] array can contain terms that
    are useless for the rule that is applied, as terms might have been saved
    because needed by another rule which is not the one applied.  The
    {!field:slot} keeps track of how many variables have been encountered
    so far and thus indicates the index in [vars] that will be used by the
    next variable. *)

(** [fetch l d e r] consumes [l] until environment builder [e] contains as
    many elements as the number of variables in [r].  The environment builder
    [e] is also enriched.  The tree which allows this consumption is returned,
    with a leaf holding action [r] and the new environment.

    The remaining terms are all consumed to expunge the stack during
    evaluation. *)
let fetch : term array -> int -> (int * int) list -> action -> t =
  fun line depth env_builder rhs ->
    let defnd = { swap = 0 ; store = false ; children = TcMap.empty
                ; default = None ; abstraction = None } in
    let terms = Array.to_list line in
    let rec loop telst added env_builder =
      match telst with
      | []       -> Leaf(env_builder, rhs)
      | te :: tl ->
          let h, args = get_args te in
          let atl = args @ tl in
          begin match h with
          | Patt(Some(i), _, _) ->
              let neb = (depth + added, i) :: env_builder in
              let child = loop atl (succ added) neb in
              Node( { defnd with store = true ; default = Some(child) })
          | Abst(_, b)          ->
              let _, body = Bindlib.unbind b in
              let child = loop (body :: atl) added env_builder in
              Node({ defnd with default = Some(child) })
          | Patt(None, _, _)    ->
              let child = loop atl added env_builder in
              Node({ defnd with default = Some(child) })
          | _                   -> Fail
          end in
    loop terms 0 env_builder

(** [compile m] returns the decision tree allowing to parse efficiently the
    pattern matching problem contained in pattern matrix [m]. *)
let rec compile : Cm.t -> t =
  let varcount = ref 0 in
  fun patterns ->
  let { Cm.clauses ; Cm.slot ; Cm.positions } = patterns in
  if Cm.is_empty patterns then Fail
  else match Cm.yield patterns with
  | Yield({ Cm.rhs ; Cm.lhs ; env_builder ; _ }) ->
      fetch lhs slot env_builder rhs
  | NlConstrain(constr)                          ->
      let ok = let nclauses = Cm.nl_succeed constr clauses in
               compile { patterns with Cm.clauses = nclauses } in
      let fail = let nclauses = Cm.nl_fail constr clauses in
                 compile {patterns with Cm.clauses = nclauses } in
      let vi, vj = NlConstraints.export constr in
      let condition = TcstrEq(vi, vj) in
      Condition({ ok ; condition ; fail })
  | FvConstrain(constr)                          ->
      let ok = let clauses = Cm.fv_succeed constr clauses in
        compile { patterns with Cm.clauses } in
      let fail = let clauses = Cm.fv_fail constr clauses in
        compile { patterns with Cm.clauses } in
      let slot, vars = FvConstraints.export constr in
      let condition = TcstrFreeVars(vars, slot) in
      Condition({ ok ; condition ; fail })
  | Specialise(swap)                             ->
      let _, pos, _ = ReductionStack.destruct positions swap in
      let store = Cm.store patterns swap in
      let updated = List.map (Cm.update_aux swap pos slot) clauses in
      let slot = if store then succ slot else slot in
      let cons = Cm.get_col swap patterns |> Cm.get_cons in
      (* Constructors specialisation *)
      let spepatts =
        let f acc (tr_cons, te_cons) =
          if tr_cons = TcAbst then acc else
          let positions, clauses = Cm.specialize te_cons swap positions
              updated in
          let ncm = { Cm.clauses ; Cm.slot ; Cm.positions } in
          TcMap.add tr_cons ncm acc in
        List.fold_left f TcMap.empty cons in
      let children = TcMap.map compile spepatts in
      (* Default child *)
      let default =
        let positions, clauses = Cm.default swap positions updated in
        let ncm = { Cm.clauses ; Cm.slot ; Cm.positions } in
        if Cm.is_empty ncm then None else Some(compile ncm) in
      (* Abstraction specialisation*)
      let abstraction =
        if List.for_all (fun (x, _) -> x <> TcAbst) cons then None else
        let var = Bindlib.new_var mkfree ("tr" ^ (string_of_int !varcount)) in
        incr varcount ;
        let positions, clauses = Cm.abstract swap var positions updated in
        let ncm = { Cm.clauses ; Cm.slot ; Cm.positions } in
        Some(var, compile ncm) in
      Node({ swap ; store ; children ; abstraction ; default })
