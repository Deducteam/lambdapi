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
      F.fprintf ppf "@ %d -- %d [label=<%a>];" father_l !nodecount pp_dotterm
        swon
    | Node(ndata)        ->
      let { swap ; children ; store ; default } = ndata in
      incr nodecount ;
      let tag = !nodecount in
      (* Create node *)
      F.fprintf ppf "@ %d [label=\"%d\"%s];" tag swap
        (if store then " shape=\"box\"" else "") ;
      (* Create edge *)
      F.fprintf ppf "@ %d -- %d [label=<%a>];" father_l tag pp_dotterm swon ;
      TcMap.iter (fun s e -> write_tree tag (DotCons(s)) e) children ;
      Option.iter (write_tree tag DotDefa) default ;
    | Fetch(store, next) ->
      incr nodecount ;
      let tag = !nodecount in
      let store_tag = if store then "s" else "" in
      F.fprintf ppf "@ %d [label=<%s> shape=\"diamond\"]" tag store_tag ;
      F.fprintf ppf "@ %d -- %d [label=<%a>];" father_l tag pp_dotterm swon ;
      write_tree tag DotDefa next
    | Fail               ->
      incr nodecount ;
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
    | Leaf(_)                                -> ()
    | _                                      -> assert false
  end ;
  F.fprintf ppf "@.}@\n@?" ;
  close_out ochan

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

  (** [pp_component o c] prints component [c] to channel [o]. *)
  let pp_component : component pp = fun oc (te, pos) ->
    Format.fprintf oc "@[<h>%a@ %@@ %a@]" Print.pp te Subterm.pp pos

  (** A redefinition of the rule type.

      {b Note} that {!type:array} is used while {!module:ReductionStack} could
      be used because {!val:pick_best_among} goes through all items of a rule
      anyway ([max(S) = Θ(|S|)]).  Since heuristics need to access elements of
      the matrix, we favour quick access with {!type:array}. *)
  type rule = { lhs : component array
              (** Left hand side of a rule.   *)
              ; rhs : action
              (** Right hand side of a rule. *)
              ; variables : int SubtMap.t
              (** Mapping from positions of variable subterms in [lhs] to a
                  slot in a term env. *)}

  (** Type of a matrix of patterns.  Each line is a row having an attached
      action. *)
  type t =
    { clauses : rule list
    (** The rules. *)
    ; var_catalogue : Subterm.t list
    (** Say {i (Mₙ)ₙ} is a finite sequence of clause matrices, where {i Mₙ₊₁}
        is either the specialisation or the default case of {i Mₙ}.  Let {i L}
        be the last matrix of the sequence.  Then {!field:var_catalogue} of {i
        L} contains positions of terms in any {!field:lhs} of any
        matrix of {i (Mₙ)ₙ} that can be used in a {!field:rhs} (of any matrix
        in {i (Mₙ)ₙ}). *) }

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

  (** [flushout_vars l] returns a mapping from position of variables into [l]
      to the slot assigned to each variable in a {!type:term_env}. *)
  let flushout_vars : term list -> int SubtMap.t = fun lhs ->
    let rec loop found st po =
      match st with
      | [] -> SubtMap.empty
      | x :: xs ->
         begin
           match x with
           | Patt(None, _, _)
           | Vari(_)
           | Symb(_, _)          -> loop found xs (Subterm.succ po)
           | Patt(Some(i), _, _) -> SubtMap.add po i
              (loop (succ found) xs (Subterm.succ po))
           | Appl(_, _)          -> let _, args = get_args x in
                                   deepen found args xs po
           | Abst(_, b)          -> let _, body = Bindlib.unbind b in
                                   deepen found [body] xs po
           | _                   -> assert false
         end
    and deepen found args remain po =
      let argpos = loop found args (Subterm.sub po) in
      SubtMap.union (fun _ _ _ -> assert false) argpos
        (loop found remain (Subterm.succ po)) in
    (* The terms of the list are the subterms of the head symbol. *)
    loop 0 lhs (Subterm.succ Subterm.init)

  (** [of_rules r] creates the initial pattern matrix from a list of rewriting
      rules. *)
  let of_rules : Terms.rule list -> t = fun rs ->
    let r2r : Terms.rule -> rule = fun r ->
      let variables = flushout_vars r.Terms.lhs in
      let term_pos = List.to_seq r.Terms.lhs |> Subterm.tag |> Array.of_seq in
      { lhs = term_pos ; rhs = r.Terms.rhs
      ; variables = variables} in
    { clauses = List.map r2r rs ; var_catalogue = [] }

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
      among columns [c] according to a heuristic. *)
  let pick_best_among : t -> int array -> int = fun mat columns->
    let wild_pc = Array.map (fun ci ->
      let c = get_col ci mat in score c) columns in
    Array.argmax (<=) wild_pc

  (** [yield m] yields a rule to be applied. *)
  let yield : t -> rule option = fun { clauses ; _ } ->
    let is_exhausted { lhs ; _ } =
      Array.for_all (fun (e, _) -> not (is_treecons e)) lhs in
    List.find_opt is_exhausted clauses

  (** [can_switch_on p k] returns whether a switch can be carried out on
      column [k] in matrix [p] *)
  let can_switch_on : t -> int -> bool = fun { clauses ; _ } k ->
    let rec loop : rule list -> bool = function
      | []      -> false
      | r :: rs -> if is_treecons (fst r.lhs.(k)) then true else loop rs in
    loop clauses

  (** [discard_cons_free m] returns the list of indexes of columns containing
      terms that can be matched against (discard constructor-free columns). *)
  let discard_cons_free : t -> int array = fun m ->
    let ncols = List.extremum (>)
      (List.map (fun { lhs ; _ } -> Array.length lhs) m.clauses) in
    let switchable = List.init ncols (can_switch_on m) in
    let switchable2ind i e = if e then Some(i) else None in
    switchable |> List.filteri_map switchable2ind |> Array.of_list

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

  (** [in_rhs] returns whether a list of term contains a term needed in the
      right hand side of a rule. *)
  let rec in_rhs : term list -> bool = function
    | []                       -> false
    | Patt(Some(_), _, _) :: _ -> true
    | _ :: xs                  -> in_rhs xs

  (** [varpos p c] returns the list of positions of pattern variables in
      column [c] of [p]. *)
  let varpos : t -> int -> Subterm.t list = fun pm ci ->
    let is_var (te, _) = match te with
      | Patt(Some(_), _, _) -> true
      | _                   -> false in
    (* We do not care about keeping the order of the new variables in [vars]
       since for any rule, at most one of them will be chosen. *)
    get_col ci pm |> List.filter is_var |> List.split |> snd
                  |> List.sort_uniq Subterm.compare

(** [spec_filter p e] returns whether a line been inspected on element [e]
    (from a pattern matrix) must be kept when specializing the matrix on
    pattern [p]. *)
  let spec_filter : term -> term -> bool = fun pat hd ->
    let h, args = get_args hd in
    let ph, pargs = get_args pat in
    match ph, h with
    | Symb(_, _), Symb(_, _)
    | Vari(_)   , Vari(_)       -> List.same_length args pargs && eq ph h
    | _         , Patt(_, _, e) ->
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
      Seq.make arity (Patt(None, "", e))
        |> Subterm.tag
        |> Seq.map (fun (te, po) -> (te, Subterm.prefix p po))
        |> Array.of_seq
    | _             -> assert false

(** [specialize p c m] specializes the matrix [m] when matching pattern [p]
    against column [c].  A matrix can be specialized by a user defined symbol.
    In case an {!constructor:Appl} is given as pattern [p], only terms having
    the same number of arguments and the same leftmost {e non}
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
    with a leaf holding action [r] and the new environment.  The strategy is
    for the moment rather stupid, nodes are consumed linearly (no swaps
    performed). *)
let fetch : Cm.component array -> int -> (int * int) list -> action -> t =
  fun line depth env_builder rhs ->
    let terms, _ = Array.split line in
    let missing = Bindlib.mbinder_arity rhs - (List.length env_builder) in
    let rec loop telst added env_builder =
      if added = missing then Leaf(env_builder, rhs) else
      match telst with
      | []       -> assert false
      | te :: tl ->
         let h, args = get_args te in
         let atl = args @ tl in
         begin match h with
         | Patt(Some(i), _, _) ->
            let neb = (depth + added, i) :: env_builder in
            let child = loop atl (succ added) neb in
            Fetch(true, child)
         | Abst(_, b)          ->
            let _, body = Bindlib.unbind b in
            let child = loop (body :: atl) added env_builder in
            Fetch(false, child)
         | Patt(None, _, _)    ->
            let child = loop atl added env_builder in
            Fetch(false, child)
         | _                   -> Fail
         end in
    loop terms 0 env_builder

(** [compile m] returns the decision tree allowing to parse efficiently the
    pattern matching problem contained in pattern matrix [m]. *)
let rec compile : Cm.t -> t = fun patterns ->
  let { Cm.var_catalogue = vcat ; _ } = patterns in
  if Cm.is_empty patterns then Fail
  else match Cm.yield patterns with
  | Some({ Cm.rhs ; Cm.lhs ; Cm.variables = pos2slot }) ->
    let f (count, acc) tpos =
      let opslot = SubtMap.find_opt tpos pos2slot in
      match opslot with
      | None     -> succ count, acc
      (* ^ Discard useless variables *)
      | Some(sl) -> succ count, (count, sl) :: acc in
    let _, env_builder = List.fold_left f (0, []) (List.rev vcat) in
    (* ^ For now, [env_builder] contains only the variables encountered
       while choosing the rule.  Other pattern variables needed in the
       rhs, which are still in the [lhs] will now be fetched. *)
    assert (List.length env_builder <= SubtMap.cardinal pos2slot) ;
    let depth = List.length vcat in
    fetch lhs depth env_builder rhs
  | None                                                ->
    let absolute_cind = (* Index of column switched on *)
      let kept_cols = Cm.discard_cons_free patterns in
      let sel_in_partial = Cm.pick_best_among patterns kept_cols in
      kept_cols.(sel_in_partial) in
    let terms, _ = List.split @@ Cm.get_col absolute_cind patterns in
    let store = Cm.in_rhs terms in
    let newcat = (* New var catalogue *)
      let newvars = Cm.varpos patterns absolute_cind in
      newvars @ patterns.Cm.var_catalogue in
    let spepatts = (* Specialization sub-matrices *)
      let cons = Cm.get_cons terms in
      let f acc (tr_cons, te_cons) =
        let rules = Cm.specialize te_cons absolute_cind patterns.clauses in
        let ncm = { Cm.clauses = rules ; Cm.var_catalogue = newcat } in
        TcMap.add tr_cons ncm acc in
      List.fold_left f TcMap.empty cons in
    let children = TcMap.map compile spepatts in
    let defmat = (* Default matrix *)
      let rules = Cm.default absolute_cind patterns.clauses in
      let ncm = { Cm.clauses = rules ; Cm.var_catalogue = newcat } in
      if Cm.is_empty ncm then None else Some(compile ncm) in
    Node({ swap = absolute_cind ; store = store ; children = children
         ; default = defmat })
