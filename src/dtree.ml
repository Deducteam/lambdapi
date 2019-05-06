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

(** An exception raised if trying to match an abstraction or a left non linear
    variable. *)
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
    └–S–∘–?–∘ → S (S m)
    v}
    with [∘] being a node (with a label not shown here) and [–u–]
    being an edge with a matching on symbol [u] or a variable or wildcard when
    [?].  Typically, the portion [S–∘–Z] is made possible by a swap. *)

(** {3 Reduction substrate} *)

(** Element consumed when reducing terms.  When reducing, we must have
    - fast access to any element in the substrate (for swaps)
    - fast replacement of an element and extension to replace an element of
    the substrate by its reduced form, or an unfolding of
    {!constructor:Appl} nodes. *)
module type Reduction_substrate =
sig
  (** Type of a substrate of ['a]. *)
  type 'a t

  (** The empty substrate. *)
  val empty : 'a t

  (** [is_empty v] returns whether a stack is empty. *)
  val is_empty : 'a t -> bool

  (** [of_list l] returns a stack containing the elements of [l]. *)
  val of_list : 'a list -> 'a t

  (** [to_list s] returns a list containing the elements of the stack [s]. *)
  val to_list : 'a t -> 'a list

  (** [length v] is the number of elements in [v]. *)
  val length : 'a t -> int

  (** Prefix and suffix of the substrate. *)
  type 'a prefix
  type 'a suffix

  (** [destruct v i] returns a triplet [(l, m, r)] with [l]eft being the
      elements from 0 to [i - 1], [m]iddle the [i]th element and [r]ight the
      elements from [i + 1] to the end of [v].
      @raise invalid_arg when [i < 0]
      @raise Not_found when [i ≥ length v]. *)
  val destruct : 'a t -> int -> 'a prefix * 'a * 'a suffix

  (** [restruct r n o] is the concatenation of three stacks [r] [n] and
      [o]. *)
  val restruct : 'a prefix -> 'a list -> 'a suffix -> 'a t
end

(** Naive implementation based on lists.  Appeared to be faster than tree
    based structures (like ropes). *)
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

  (** [restruct l c r] complexity in [Θ(length l)]*)
  let restruct l c r =
    let rec insert acc l =
      match l with
      | []   -> acc
      | x::l -> insert (x :: acc) l
    in
    insert (c @ r) l
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
    | DotCons(t) -> F.fprintf oc "%s<sub>%d</sub>" t.c_sym t.c_ari in
  (* [write_tree n u v] writes tree [v] obtained from tree number [n] with a
     switch on [u] ({!constructor:None} if default). *)
  let rec write_tree : int -> dot_term -> t -> unit =
    fun father_l swon tree ->
      match tree with
      | Leaf(_, a)         ->
          incr nodecount ;
        let _, acte = Bindlib.unmbind a in
        F.fprintf ppf "@ %d [label=\"%a\"];" !nodecount P.pp acte ;
        F.fprintf ppf "@ %d -- %d [label=<%a>];" father_l !nodecount
          pp_dotterm swon
      | Node(ndata)        ->
          let { swap ; children ; store ; default } = ndata in
          incr nodecount ;
          let tag = !nodecount in
          (* Create node *)
          F.fprintf ppf "@ %d [label=\"@%d\"%s];" tag swap
            (if store then " shape=\"box\"" else "") ;
          (* Create edge *)
          F.fprintf ppf "@ %d -- %d [label=<%a>];" father_l tag pp_dotterm
            swon ;
          TcMap.iter (fun s e -> write_tree tag (DotCons(s)) e) children ;
          Option.iter (write_tree tag DotDefa) default ;
      | Condition(cdata) ->
          let { ok ; condition ; fail } = cdata in
          incr nodecount ;
          let tag = !nodecount in
          F.fprintf ppf
            "@ %d [label=<%s<sub>%d</sub>> shape=\"diamond\"];" tag
            (match condition with TcstrEq(_) -> "≡" | TcstrFreeVars(_) ->
              "FV")
            (match condition with TcstrEq(i, _) -> i | TcstrFreeVars(_) -> 0) ;
          F.fprintf ppf
            "@ %d -- %d [label=<%a>];" father_l tag pp_dotterm swon ;
          write_tree tag DotDefa ok ;
          write_tree tag DotDefa fail ;
      | Fail               ->
          incr nodecount ;
        F.fprintf ppf "@ %d [label=<!>];" !nodecount ;
        F.fprintf ppf "@ %d -- %d [label=\"!\"];" father_l !nodecount
  in
  begin
    match tree with
    (* First step must be done to avoid drawing a top node. *)
    | Node({ swap ; children = ch ; store ; default }) ->
        F.fprintf ppf "@ 0 [label=\"%d\"%s];"
          swap (if store then " shape=\"box\"" else "") ;
        TcMap.iter (fun sw c -> write_tree 0 (DotCons(sw)) c) ch ;
        (match default with None -> () | Some(tr) -> write_tree 0 DotDefa tr)
    | Leaf(_)                                          -> ()
    | _                                                -> assert false
  end ;
  F.fprintf ppf "@.}@\n@?" ;
  close_out ochan

(** {3 Constraint structure} *)
module type BinConstraintPoolSig =
sig
  (** Set of constraints declared, either available or not. *)
  type t

  (** A unique instantiated constraint. *)
  type cstr

  (** [pp_cstr o c] prints constraint [c] to channel [o]. *)
  val pp_cstr : cstr pp

  (** [pp o p] prints pool [p] to channel [o]. *)
  val pp : t pp

  (** The empty set of constraints. *)
  val empty : t

  (** [is_empty p] returns whether pool [p] is empty. *)
  val is_empty : t -> bool

  (** [concerns p q] @return whether position [p] is constrained in pool [q]. *)
  val concerns : Subterm.t -> t -> bool

  (** [has c p] returns whether pool [p] has constraint [c] instantiated. *)
  val has : cstr -> t -> bool

  (** [remove c p] removes constraint [c] from pool [p]. *)
  val remove : cstr -> t -> t

  (** [instantiate p i q] instantiates path [p] in pool [q], that is, make a
      constraint partially instantiated if none of the paths were instantiated
      or make it available if one path was already instantiated.  Uses index
      [i] as support of the constraint.
      @raise Not_found if [p] is not part of any constraint in [q]. *)
  val instantiate : Subterm.t -> int -> t -> t

  (** [of_terms r] returns nonlinearity constraints induced by terms in
      [r]. *)
  val of_terms : term list -> t
end

module type NlConstraintSig =
sig
  include BinConstraintPoolSig

  (** Action to perform. *)
  type decision =
    | Solve of cstr * int
    (** A constraint to apply along with its heuristic score. *)
    | Instantiate of Subterm.t * int
    (** Carry out a switch on a term specified by its position, score. *)
    | Unavailable
    (** No non linearity constraint available. *)

  (** [choose p] returns the constraint with the highest priority in [p]. *)
  val choose : t list -> decision

  (** [to_varindexes c] returns the indexes containing terms bound by a
      constraint in the [vars] array. *)
  val to_varindexes : cstr -> int * int
end

(** Manages non linearity constraints *)
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

  type decision =
    | Solve of cstr * int
    | Instantiate of Subterm.t * int
    | Unavailable

  let pp_cstr oc (i, j) = Format.fprintf oc "(%d,%d)" i j

  let pp oc pool =
    let module F = Format in
    let pp_subtset oc ss =
      F.fprintf oc "@[<h>{" ;
      F.pp_print_list ~pp_sep:(fun oc () -> F.pp_print_string oc ";")
        Subterm.pp oc (SubtSet.elements ss) ;
      F.fprintf oc "}@]" in
    let pp_int_subtset oc (i, ss) =
      F.fprintf oc "@[<h>(%d, %a)@]" i pp_subtset ss in
    let pp_groups oc pgroups =
      F.pp_print_string oc "groups:" ;
      F.fprintf oc "@[<v 2>" ;
      F.pp_print_list ~pp_sep:(F.pp_print_cut) pp_int_subtset oc
        pgroups ;
      F.pp_close_box oc () in
    let pp_subterm_int oc (st, i) =
      F.fprintf oc "@[<h>(%a, %d)@]" Subterm.pp st i in
    let pp_partial oc ism =
      F.fprintf oc "partial: @[<h>" ;
      F.pp_print_list ~pp_sep:(fun oc () -> F.pp_print_string oc ";")
        pp_subterm_int oc (SubtMap.bindings ism) ;
      F.pp_close_box oc () in
    let pp_int_int oc (i, j) = F.fprintf oc "@[<h>(%d, %d)@]" i j in
    let pp_available oc ips =
      F.fprintf oc "available: @[<h>" ;
      F.pp_print_list ~pp_sep:(fun oc () -> F.pp_print_string oc ";")
        pp_int_int oc (IntPairSet.elements ips) ;
      F.pp_close_box oc () in
    F.fprintf oc "{@[<v>@," ;
    F.fprintf oc "@[<h>%a@]@," pp_groups pool.groups ;
    F.fprintf oc "@[<h>%a@]@," pp_partial pool.partial ;
    F.fprintf oc "@[<h>%a@]" pp_available pool.available ;
    F.fprintf oc "@.@]}"

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
            (fun c -> c.partial |> SubtMap.bindings |> List.split |> fst |>
                      List.append) cstrs [] |> List.sort_uniq Subterm.compare in
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

  let has pair { available ; _ } = IntPairSet.mem pair available

  let concerns p q = SubtSet.mem p q.concerned

  let remove pair pool = { pool with
                           available = IntPairSet.remove pair pool.available }

  let to_varindexes pair = pair

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

  (** [fold_vars l f m i] is a fold-like function on pattern variables in [l].
      When a {!constructor:Patt} is found in any subterm of [l], function [f]
      is applied on the pattern variable and an accumulator.  Function [m] is
      used to combine the returned values on different subterms. *)
  let fold_vars : term list ->
    add:(Subterm.t -> int option -> string -> term array -> 'a -> 'a) ->
    merge:('a -> 'a -> 'a) ->
    init:'a -> 'a = fun lhs ~add ~merge ~init ->
      let rec loop st po =
        match st with
        | [] -> init
        | x :: xs ->
            begin match x with
            | Patt(None, _, _)
            | Vari(_)
            | Symb(_, _)    -> loop xs (Subterm.succ po)
            | Patt(i, s, e) -> add po i s e (loop xs (Subterm.succ po))
            | Appl(_, _)    -> let _, args = get_args x in
                              deepen args xs po
            | Abst(_, b)    -> let _, body = Bindlib.unbind b in
                              deepen [body] xs po
            | _             -> assert false
            end
      and deepen args remain po =
        let argpos = loop args (Subterm.sub po) in
        let next = loop remain (Subterm.succ po) in
        merge argpos next in
      (* The terms of the list are the subterms of the head symbol. *)
      loop lhs (Subterm.succ Subterm.init)

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

(** {3 Clause matrix and pattern matching problem} *)

(** A clause matrix encodes a pattern matching problem.  The clause matrix {i
    C} can be denoted {i C = P → A} where {i P} is a {e pattern matrix} and {i
    A} is a column of {e actions}.  Each line of a pattern matrix is a pattern
    to which is attached an action.  When reducing a term, if a line filters
    the term, or equivalently the term matches the pattern, the term is
    rewritten to the action. *)
module ClauseMat =
struct

  (** A component of the matrix, a term along with its position in the top
      term. *)
  type component = term * Subterm.t

  (** A redefinition of the rule type.

      {b Note} that {!type:array} is used while {!module:ReductionStack} could
      be used because {!val:pick_best_among} goes through all items of a rule
      anyway ([max(S) = Θ(|S|)]).  Since heuristics need to access elements of
      the matrix, we favour quick access with {!type:array}. *)
  type rule =
    { lhs : component array
    (** Left hand side of a rule.   *)
    ; rhs : action
    (** Right hand side of a rule. *)
    ; env_builder : (int * int) list
    ; nonlin : NlConstraints.t }

  (** Type of a matrix of patterns.  Each line is a row having an attached
      action. *)
  type t =
    { clauses : rule list
    (** The rules. *)
    ; var_met : int
    (** Number of variables met so far. *) }

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

  (** [pp_component o c] prints component [c] to channel [o]. *)
  let pp_component : component pp = fun oc (te, pos) ->
    Format.fprintf oc "@[<h>%a@ %@@ %a@]" Print.pp te Subterm.pp pos

  (** [pp o m] prints matrix [m] to out channel [o]. *)
  let pp : t pp = fun oc { clauses ; _ } ->
    let module F = Format in
    let pp_line oc l =
      F.fprintf oc "@[<h>" ;
      F.pp_print_list ~pp_sep:(fun _ () -> F.fprintf oc ";@ ")
        pp_component oc (Array.to_list l) ;
      F.fprintf oc "@]" in
    F.fprintf oc "{@[<v>@," ;
    F.pp_print_list ~pp_sep:F.pp_print_cut pp_line oc
      (List.map (fun { lhs ; _ } -> lhs) clauses) ;
    F.fprintf oc "@.}@,"

  (** [of_rules r] creates the initial pattern matrix from a list of rewriting
      rules. *)
  let of_rules : Terms.rule list -> t = fun rs ->
    let r2r : Terms.rule -> rule = fun r ->
      let term_pos = List.to_seq r.Terms.lhs |> Subterm.tag |> Array.of_seq in
      let nonlin = NlConstraints.of_terms r.lhs in
      { lhs = term_pos ; rhs = r.Terms.rhs ; nonlin ; env_builder = [] } in
    { clauses = List.map r2r rs ; var_met = 0 }

  (** [is_empty m] returns whether matrix [m] is empty. *)
  let is_empty : t -> bool = fun m -> m.clauses = []

  (** [get_col n m] retrieves column [n] of matrix [m]. *)
  let get_col : int -> t -> component list = fun ind { clauses ; _ } ->
    List.map (fun { lhs ; _ } -> lhs.(ind)) clauses

  (** [score c] returns the score heuristic for column [c]. *)
  let rec score : component list -> int = function
    | []                              -> 0
    | (x, _) :: xs when is_treecons x -> score xs
    | _ :: xs                         -> succ (score xs)

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
      | r :: rs -> if is_treecons (fst r.lhs.(k)) then true else loop rs in
    loop clauses

  (** [is_exhausted r] returns whether [r] can be applied or not. *)
  let is_exhausted : rule -> bool = fun { lhs ; nonlin ; _ } ->
    Array.for_all (fun (e, _) -> not (is_treecons e)) lhs &&
    NlConstraints.is_empty nonlin

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

  (** [yield m] yields a rule to be applied. *)
  let yield : t -> decision = fun m ->
    let { clauses ; _ } = m in
    let positions = (List.hd m.clauses).lhs |> Array.split |>
                       snd |> Array.of_list in
    match List.find_opt is_exhausted clauses with
    | Some(r) -> Yield(r)
    | None    ->
        let nlcstrs = List.map (fun r -> r.nonlin) m.clauses in
        match NlConstraints.choose nlcstrs, choose m with
        | Unavailable  , None        -> assert false
        | Unavailable  , Some(ci, _) -> Specialise(ci)
        | Instantiate(p, _), None    ->
            let col = Array.search (fun x -> Subterm.compare x p)
                        positions in
            Specialise(col)
        | Instantiate(_, _), Some(cic, _) -> Specialise(cic)
        (* A case should be added when instantiate score is higher, this would
           imply that a non linear constraint can motivate a specialisation in
           order to reach a constraint. *)
        | Solve(c, _), None          -> NlConstrain(c)
        | Solve(c, scs), Some(_, scc)
          when scs > scc             -> NlConstrain(c)
        | Solve(_, scs), Some(cic, scc)
          when scs <= scc            -> Specialise(cic)
        | _            , _           -> assert false

  (** [get_cons l] extracts, sorts and uniqify terms that are tree
      constructors in [l].  The actual tree constructor (of type
      {!type:treecons}) is returned along the original term. *)
  let get_cons : term list -> (treecons * term) list = fun telst ->
    let keep_treecons e =
      if is_treecons e then Some(treecons_of_term e, e) else None in
    let tc_fst_cmp (tca, _) (tcb, _) = tc_compare tca tcb in
    telst |> List.filter_map keep_treecons |> List.sort_uniq tc_fst_cmp

  (** [contains_abst l] returns whether list of terms [l] contains an
      abstraction. *)
  let rec contains_abst : term list -> bool = function
    | [] -> false
    | Abst(_, _) :: _  -> true
    | _          :: xs -> contains_abst xs

  (** [contains_var l] returns whether list of terms [l] contains a pattern
      variable with a slot assigned. *)
  let rec contains_var : term list -> bool = function
    | []                        -> false
    | Patt(Some(_), _, _) :: _  -> true
    | _                   :: xs -> contains_var xs

  (** [in_rhs] returns whether a list of term contains a term needed in the
      right hand side of a rule. *)
  let rec in_rhs : term list -> bool = function
    | []                       -> false
    | Patt(Some(_), _, _) :: _ -> true
    | _ :: xs                  -> in_rhs xs

  (** [update_aux c v r] returns rule [r] with auxiliary data updated
      (i.e. non linearity constraints and environment builder). *)
  let update_aux : int -> int -> rule -> rule = fun ci var_met r ->
    let t, p = r.lhs.(ci) in
    match fst (get_args t) with
    | Patt(Some(i), _, _) ->
        let env_builder = (var_met, i) :: r.env_builder in
        let nonlin = if NlConstraints.concerns p r.nonlin
          then NlConstraints.instantiate p var_met r.nonlin
          else r.nonlin in
        { r with env_builder ; nonlin }
    | _                   -> r

  (** [spec_filter p e] returns whether a line been inspected on element [e]
      (from a pattern matrix) must be kept when specializing the matrix on
      pattern [p].
      @raise Invalid_argument when the element [e] is ill formed. *)
  let spec_filter : term -> term -> bool = fun pat hd ->
    let h, args = get_args hd in
    let ph, pargs = get_args pat in
    match ph, h with
    | Symb(_, _), Symb(_, _)
    | Vari(_)   , Vari(_)       -> List.same_length args pargs && eq ph h
    | _         , Patt(_, _, e) ->
        if args <> [] then invalid_arg "ClauseMat.spec_filter" else
          let b = Bindlib.bind_mvar (Array.map to_tvar e) (lift ph) in
          Bindlib.is_closed b
    | _         , _             -> false

  (** [spec_transform p e] transform element [e] (from a lhs) when
      specializing against pattern [p]. *)
  let spec_transform : term -> component -> component array =
    fun pat (t, p) ->
      let h, args = Basics.get_args t in
      match h with
      | Symb(_, _)
      | Vari(_)       ->
          let np = Subterm.sub p in
          args |> List.to_seq |> Subterm.tag ~empty:np |> Array.of_seq
      | Patt(_, _, e) ->
          let arity = pat |> Basics.get_args |> snd |> List.length in
          Seq.make arity (Patt(None, "", e)) |> Subterm.tag |>
              Seq.map (fun (te, po) -> (te, Subterm.prefix p po)) |>
              Array.of_seq
      | _             -> assert false

  (** [specialize p c m] specializes the matrix [m] when matching pattern [p]
      against column [c].  A matrix can be specialized by a user defined
      symbol.  In case an {!constructor:Appl} is given as pattern [p], only
      terms having the same number of arguments and the same leftmost {e non}
      {!constructor:Appl} term match. *)
  let specialize : term -> int -> rule list -> rule list = fun p ci rs ->
    let filtered = List.filter (fun { lhs ; _} ->
      spec_filter p (fst lhs.(ci))) rs in
    let newcith = List.map (fun { lhs ; _ } -> spec_transform p lhs.(ci))
      filtered in
    List.map2 (fun newcith rul ->
      let { lhs ; _ } = rul in
      let postfix = Array.drop (ci + 1) lhs in
      let newline = Array.concat
        [ Array.sub lhs 0 ci
        ; newcith
        ; postfix ] in
      { rul with lhs = newline }) newcith filtered

  (** [default c m] computes the default matrix containing what remains to be
      matched in case the pattern used is not in the column [c]. *)
  let default : int -> rule list -> rule list = fun ci rs ->
    let filtered = List.filter (fun { lhs ; _ } ->
      match fst @@ lhs.(ci) with
      | Patt(_ , _, _) -> true
      | Symb(_, _)
      | Abst(_, _)
      | Vari(_)
      | Appl(_, _)     -> false
      | _              -> assert false) rs in
    List.map (fun rul ->
      let { lhs ; _ } = rul in
      match lhs.(ci) with
      | Patt(_, _, _), _ ->
          let postfix = Array.drop (ci + 1) lhs in
          { rul with lhs = Array.append (Array.sub lhs 0 ci) postfix  }
      | _                -> assert false) filtered

  (** [nl_succeed c r] computes the rule list from [r] that verify a
      non-linearity constraint [c]. *)
  let nl_succeed : NlConstraints.cstr -> rule list -> rule list = fun c ->
    let f r =
      let { nonlin ; _ } = r in
      let nonlin = NlConstraints.remove c nonlin in
      { r with nonlin } in
    List.map f

  (** [nl_fail c r] computes the rules not failing a non-linearity constraint
      [c] among rules [r]. *)
  let nl_fail : NlConstraints.cstr -> rule list -> rule list = fun c ->
    let f { nonlin ; _ } = not (NlConstraints.has c nonlin) in
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

    The last is managed by the {!val:env_builder} as follows.  The matching
    process uses, along with the tree, an array to store terms that may be
    used in a candidate {!field:rhs}.  Terms are stored while parsing if the
    {!constructor:Node} has its {!field:store} at {!val:true}.  To know when
    to store variables, each rule is first parsed with {!val:Cm.flushout_vars}
    to get the positions of {!constructor:Patt} in each {!field:lhs}.  Once
    these positions are known, the {!field:Cm.var_catalogue} can be built.  A
    {!field:Cm.var_catalogue} contains the accumulation of the positions of
    terms used in {!field:rhs}s encountered so far during successive
    branchings.  Once a rule can be triggered, {!field:Cm.var_catalogue}
    contains, in the order they appear during matching, all the terms the
    rule can use, that are the terms {e that have been inspected}.  There
    may remain terms that haven't been inspected (because they are not needed
    to decide which rule to apply), but that are nevertheless needed in the
    {!field:rhs}.  Note that the {!field:Cm.var_catalogue} contains useless
    variables as well: these may have been needed by other rules, when several
    rules were still candidates.  The {!val:env_builder} is then initialized
    and contains only essential terms from the catalogue for the rule to
    apply.  The remaining variables, which will remain in the input stack will
    be fetched thanks to a subtree built by {!val:fetch}. *)

(** [fetch l d e r] consumes [l] until environment builder [e] contains as
    many elements as the number of variables in [r].  The environment builder
    [e] is also enriched.  The tree which allows this consumption is returned,
    with a leaf holding action [r] and the new environment.

    The remaining terms are all consumed to expunge the stack during
    evaluation. *)
let fetch : Cm.component array -> int -> (int * int) list -> action -> t =
  fun line depth env_builder rhs ->
    let defnd = { swap = 0 ; store = false ; children = TcMap.empty
                ; default = None } in
    let terms, _ = Array.split line in
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
let rec compile : Cm.t -> t = fun patterns ->
  let { Cm.clauses ; Cm.var_met } = patterns in
  if Cm.is_empty patterns then Fail
  else match Cm.yield patterns with
  | Yield({ Cm.rhs ; Cm.lhs ; env_builder ; _ }) ->
      fetch lhs var_met env_builder rhs
  | NlConstrain(constr)                          ->
      let ok = let nclauses = Cm.nl_succeed constr clauses in
               compile { patterns with Cm.clauses = nclauses } in
      let fail = let nclauses = Cm.nl_fail constr clauses in
                 compile {patterns with Cm.clauses = nclauses } in
      let vi, vj = NlConstraints.to_varindexes constr in
      let condition = TcstrEq(vi, vj) in
      Condition({ ok ; condition ; fail })
  | Specialise(cind)                             ->
      let terms = Cm.get_col cind patterns |> List.split |> fst in
      let store = Cm.in_rhs terms in
      let nvm = if Cm.contains_var terms then succ var_met else var_met in
      let spepatts = (* Specialization sub-matrices *)
        let cons = Cm.get_cons terms in
        let f acc (tr_cons, te_cons) =
          let rules = List.map (Cm.update_aux cind var_met) clauses |>
                      Cm.specialize te_cons cind in
          let ncm = { Cm.clauses = rules ; var_met = nvm } in
          TcMap.add tr_cons ncm acc in
        List.fold_left f TcMap.empty cons in
      let children = TcMap.map compile spepatts in
      let default = (* Default matrix *)
        let rules = List.map (Cm.update_aux cind var_met) clauses |>
                    Cm.default cind in
        let ncm = { Cm.clauses = rules ; var_met = nvm } in
        if Cm.is_empty ncm then None else Some(compile ncm) in
      Node({ swap = cind ; store ; children ; default })
