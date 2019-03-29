(** This module provides functions to compile rewrite rules to decision trees
    in order to pattern match the rules efficiently.  The method is based on
    Luc Maranget's {i Compiling Pattern Matching to Good Decision Trees},
    {{:10.1145/1411304.1411311}DOI}. *)
open Terms
open Extra
module Sub = Basics.Subterm
module SubMap = Basics.SubtMap

(** See {!type:tree} in {!module:Terms}. *)
type t = tree

(** Type of the leaves of the tree.  See {!module:Terms}, {!field:rhs}. *)
type action = (term_env, term) Bindlib.mbinder

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

(** [iter l n f t] is a generic iterator on trees; with function [l] performed
    on leaves, function [n] performed on nodes, [f] returned in case of
    {!constructor:Fail} on tree [t]. *)
let iter : do_leaf:(int IntMap.t -> action -> 'a) ->
  do_node:(int option -> bool -> 'a StrMap.t ->
           (term Bindlib.var * 'a) option -> 'a option -> 'a) ->
  fail:'a -> t -> 'a = fun ~do_leaf ~do_node ~fail t ->
  let rec loop = function
    | Leaf(pa, a)                      -> do_leaf pa a
    | Fail                             -> fail
    | Node({ swap ; store ; children ; abstspec ; default }) ->
       do_node swap store
         (StrMap.map (fun c -> loop c) children)
         (Option.map (fun (v, a) -> v, loop a) abstspec)
         (Option.map loop default) in
  loop t

(** [capacity t] computes the capacity of tree [t].  During evaluation, some
    terms that are being filtered by the patterns need to be saved in order to
    be bound in the right hand side of the rule.  The capacity is an upper
    bound of the number of terms to be saved. *)
let capacity : t -> int =
  let do_leaf _ _ = 0 in
  let fail = 0 in
  let do_node _ st ch ab de =
    let _, chdepths = List.split (StrMap.bindings ch) in
    let abdepth = match ab with None -> 0 | Some(_, d) -> d in
    let dedepth = Option.get de 0 in
    List.extremum (>) ([abdepth ; dedepth] @ chdepths) +
      (if st then 1 else 0) in
  iter ~do_leaf:do_leaf ~fail:fail ~do_node:do_node

(** [add_args_repr s a] adds the number of arguments in the representation of
    [s]. *)
let add_args_repr : string -> int -> string = fun sym nargs ->
  sym ^ (string_of_int nargs)

(** [symrepr_of_term s] extracts the name of [s] concatenated with the number
    of arguments.  Handles {!constructor:Appl} nodes. *)
let symrepr_of_term : term -> string = fun te ->
  let hd, args = Basics.get_args te in
  let nargs = List.length args in
  match hd with
  | Symb({ sym_name ; _ }, _) -> add_args_repr sym_name nargs
  | _                         -> assert false

(** Printing hint for conversion to graphviz. *)
type dot_term =
  | DotDefa
  | DotAbst of tvar
  | DotCons of string

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
    | DotCons(t) -> F.fprintf oc "%s" t in
  (* [write_tree n u v] writes tree [v] obtained from tree number [n] with a
     switch on [u] ({!constructor:None} if default). *)
  let rec write_tree : int -> dot_term -> t -> unit =
    fun father_l swon tree ->
    match tree with
    | Leaf(_, a) ->
      incr nodecount ;
      let _, acte = Bindlib.unmbind a in
      F.fprintf ppf "@ %d [label=\"%a\"];" !nodecount P.pp acte ;
      F.fprintf ppf "@ %d -- %d [label=\"%a\"];" father_l !nodecount pp_dotterm
        swon
    | Node(ndata)   ->
      let { swap ; children ; store ; abstspec ; default } = ndata in
      incr nodecount ;
      let tag = !nodecount in
      (* Create node *)
      F.fprintf ppf "@ %d [label=\"%d\"%s];" tag (Option.get swap 0)
        (if store then " shape=\"box\"" else "") ;
      (* Create edge *)
      F.fprintf ppf "@ %d -- %d [label=\"%a\"];" father_l tag pp_dotterm swon ;
      StrMap.iter (fun s e -> write_tree tag (DotCons(s)) e) children ;
      (match default with None -> () | Some(tr) -> write_tree tag DotDefa tr) ;
      begin
        match abstspec with
        | None        -> ()
        | Some(v, tr) -> write_tree tag (DotAbst(v)) tr
      end
    | Fail          ->
      incr nodecount ;
      F.fprintf ppf "@ %d -- %d [label=\"!\"];" father_l !nodecount
  in
  begin
    match tree with
    (* First step must be done to avoid drawing a top node. *)
    | Node({ swap ; children = ch ; store ; abstspec ; default }) ->
       F.fprintf ppf "@ 0 [label=\"%d\"%s];"
         (Option.get swap 0) (if store then " shape=\"box\"" else "") ;
       StrMap.iter (fun sw c -> write_tree 0 (DotCons(sw)) c) ch ;
       (match default with None -> () | Some(tr) -> write_tree 0 DotDefa tr) ;
       (
         match abstspec with
         | None        -> ()
         | Some(v, tr) -> write_tree 0 (DotAbst(v)) tr
       ) ;
    | Leaf(_)                                -> ()
    | _                                      -> assert false
  end ;
  F.fprintf ppf "@.}@\n@?" ;
  close_out ochan

(** A clause matrix encodes a pattern matching problem.  The clause matrix
    {%latex:C%} can be denote {%latex:C = P \rightarrow A%} where {i P} is a
    {e pattern matrix} and {i A} is a column of {e actions}.  Each line of a
    pattern matrix is a pattern to which is attached an action.  When reducing
    a term, if a line filters the term, or equivalently the term matches the
    pattern, the term is rewritten to the action. *)
module ClauseMat =
struct
  (** A component of the matrix, a term along with its position in the top
      term. *)
  type component = term * Basics.Subterm .t

  (** [pp_component o c] prints component [c] to channel [o]. *)
  let pp_component : component pp = fun oc (te, pos) ->
    let module F = Format in
    F.fprintf oc "@[<h>%a@ %@@ %a@]" Print.pp te Basics.Subterm.pp pos

  (** A redefinition of the rule type. *)
  type rule = { lhs : component array
              (** Left hand side of a rule. *)
              ; rhs : action
              (** Right hand side of a rule. *)
              ; variables : int SubMap.t
              (** Mapping from positions of variable subterms in [lhs] to a
                  slot in a term env. *)}

  (** Type of a matrix of patterns.  Each line is a row having an attached
      action. *)
  type t = { clauses : rule list
           (** The rules. *)
           ; var_catalogue : Sub.t list
           (** Contains positions of terms in {!field:lhs} that can be used
               as variables in any of the {!field:rhs} which appeared in
               the matrix that gave birth to this one. *)}

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
  let flushout_vars : term list -> action -> int SubMap.t = fun lhs rhs ->
    let nvars = Bindlib.mbinder_arity rhs in
    let rec loop found st po =
      if found = nvars then SubMap.empty else
      match st with
      | [] -> SubMap.empty
      | x :: xs ->
         begin
           match x with
           | Patt(None, _, _)
           | Vari(_)
           | Symb(_, _)          -> loop found xs (Sub.succ po)
           | Patt(Some(i), _, _) -> SubMap.add po i
              (loop (succ found) xs (Sub.succ po))
           | Appl(_, _)          -> let _, args = Basics.get_args x in
                                   deepen found args xs po
           | Abst(_, b)          -> let _, body = Bindlib.unbind b in
                                   deepen found [body] xs po
           | _                   -> assert false
         end
    and deepen found args remain po =
      let argpos = loop found args (Sub.sub po) in
      SubMap.union (fun _ _ _ -> assert false) argpos
        (loop found remain (Sub.succ po))
    in
    (* Start as if the terms of the list were subterms of an initial term *)
    loop 0 lhs (Sub.succ Sub.init)

  (** [of_rules r] creates the initial pattern matrix from a list of rewriting
      rules. *)
  let of_rules : Terms.rule list -> t = fun rs ->
    let r2r : Terms.rule -> rule = fun r ->
      let variables = flushout_vars r.Terms.lhs r.Terms.rhs in
      let term_pos = Sub.tag (Array.of_list r.Terms.lhs) in
      { lhs = term_pos ; rhs = r.Terms.rhs
      ; variables = variables} in
    { clauses = List.map r2r rs ; var_catalogue = [] }

  (** [is_empty m] returns whether matrix [m] is empty. *)
  let is_empty : t -> bool = fun m -> m.clauses = []

  (** [get_col n m] retrieves column [n] of matrix [m]. *)
  let get_col : int -> t -> component list = fun ind { clauses ; _ } ->
    List.map (fun { lhs ; _ } -> lhs.(ind)) clauses

  (** [is_cons t] returns whether a term [t] is considered as a constructor. *)
  let rec is_cons : term -> bool = function
    | Appl(_, _) as a -> is_cons (fst (Basics.get_args a))
    | Meta(_, _)
    | Abst(_, _)
    | Patt(_, _, _)   -> false
    | Vari(_)
    | Symb(_, _)      -> true
    | _               -> assert false

  (** [pick_best_among m c] returns the index of the best column of matrix [m]
      among columns [c] according to a heuristic. *)
  let pick_best_among : t -> int array -> int = fun mat columns->
    let rec count_non_const = function
      | []                           -> 0
      | x :: xs when is_cons (fst x) -> count_non_const xs
      | _ :: xs                      -> 1 + (count_non_const xs) in
    let wild_pc = Array.map (fun ci ->
      let c = get_col ci mat in count_non_const c) columns in
    Array.argmax (<=) wild_pc

  (** [exhausted m] returns whether clause matrix [m] can be further pattern
      matched or if it is ready to yield an action.  A rule is exhausted when
      its left hand side is composed only of wildcards. *)
  let exhausted : t -> bool = fun { clauses ; _ } ->
    let flhs = (List.hd clauses).lhs in
    Array.for_all (fun (e, _) -> not @@ is_cons e) flhs

  (** [yield m] yields a rule to be applied. *)
  let yield : t -> rule = fun { clauses ; _ } -> List.hd clauses

  (** [can_switch_on p k] returns whether a switch can be carried out on
      column [k] in matrix [p] *)
  let can_switch_on : t -> int -> bool = fun { clauses ; _ } k ->
    let rec loop : rule list -> bool = function
      | []      -> false
      | r :: rs -> if is_cons (fst r.lhs.(k)) then true else loop rs in
    loop clauses

  (** [discard_cons_free m] returns the list of indexes of columns containing
      terms that can be matched against (discard constructor-free columns). *)
  let discard_cons_free : t -> int array = fun m ->
    let ncols = List.extremum (>)
      (List.map (fun { lhs ; _ } -> Array.length lhs) m.clauses) in
    let switchable = List.init ncols (can_switch_on m) in
    let indexes = List.mapi (fun k cm ->
        if cm then Some(k) else None) switchable in
    let remaining = List.filter (function
        | None    -> false
        | Some(_) -> true) indexes in
    let unpacked = List.map (function
        | Some(k) -> k
        | None    -> assert false) remaining in
    assert (List.length unpacked > 0) ;
    Array.of_list unpacked

  (** [get_cons l] extracts a list of unique constructors from [l].  The
      returned list can contain {!constructor:Appl} nodes to keep track of the
      number of arguments. *)
  let get_cons : term list -> term list = fun telst ->
    (* [cons_eq t u] returns whether [t] and [u] are the same regarding
       specialization. *)
    let cons_eq : term -> term -> bool = fun te tf ->
      match te, tf with
      | Abst(_, _), Abst(_, _) -> true
      | _                      -> Basics.eq te tf in
  (* membership of terms *)
    let rec mem : term -> term list -> bool = fun te xs ->
      match xs with
      | []       -> false
      | hd :: tl ->
         let s = fst (Basics.get_args hd) in
         if cons_eq s te then true else mem te tl in
    let rec loop : 'a list -> 'a list -> 'a list = fun seen notseen ->
      match notseen with
      | [] -> List.rev seen
      | hd :: tl ->
         let s = fst (Basics.get_args hd) in
         loop (if not (is_cons s) || mem s seen then seen else hd :: seen) tl in
    loop [] telst

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

  (** [varpos p] returns the list of positions of pattern variables in the
      first column of [p]. *)
  let varpos : t -> int -> Sub.t list = fun pm ci ->
    let is_var (te, _) = match te with
      | Patt(Some(_), _, _) -> true
      | _                   -> false in
    let _, vars = List.split (List.filter is_var (get_col ci pm)) in
    (* We do not care about keeping the order of the new variables in [vars]
       since for any rule, at most one of them will be chosen. *)
    List.sort_uniq Sub.compare vars

(** [spec_filter p e] returns whether a line been inspected on element [e]
    (from a pattern matrix) must be kept when specializing the matrix on
    pattern [p]. *)
  let rec spec_filter : term -> term -> bool = fun pat hd ->
    match pat, hd with
    | Symb(_, _)   , Symb(_, _)
    | Vari(_)      , Vari(_)             -> Basics.eq pat hd
    | Appl(_, _)   , Appl(_, _)          ->
       let ps, pargs = Basics.get_args pat in
       let hs, hargs = Basics.get_args hd in
       spec_filter ps hs && List.same_length pargs hargs
    | Appl(_, _)   , Patt(_, _, _)       -> true
    | _            , Patt(_, _, e)       ->
       let b = Bindlib.bind_mvar (Basics.to_tvars e) (lift pat) in
       Bindlib.is_closed b
  (* All below ought to be put in catch-all case*)
    | Symb(_, _), Abst(_, _)
    | Abst(_, _), Symb(_, _)
    | Symb(_, _), Appl(_, _)
    | Appl(_, _), Symb(_, _)
    | Appl(_, _), Abst(_, _)
    | _         , Abst(_, _)
    | Abst(_, _), _          -> false
    | _                      -> assert false

  (** [spec_transform p e] transform element [e] (from a lhs) when
      specializing against pattern [p]. *)
  let rec spec_transform : term -> component -> component array = fun pat elt ->
      match elt with
      | Symb(_, _), _
      | Vari(_)   , _ -> [| |]
      | Appl(_, _), p ->
         (* ^ Arguments verified in filter *)
         let upat = fst @@ Basics.get_args pat in
         let hs, hargs = Basics.get_args (fst elt) in
         let np = Sub.sub p in
         let tagged = Sub.tag ~empty:np (Array.of_list hargs) in
         Array.append (spec_transform upat (hs, np)) tagged
      | _             -> (* Cases that require the pattern *)
      match elt, pat with
      | (Patt(_, _, e), p), Appl(_, _) ->
         let arity = List.length @@ snd @@ Basics.get_args pat in
         let tagged = Sub.tag
           (Array.init arity (fun _ -> Patt(None, "", e))) in
         (Array.map (fun (te, po) -> (te, Sub.prefix p po)) tagged)
      | (Patt(_, _, _), _)    , _      -> [| |]
      | _                              -> assert false

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
      let postfix = if ci >= Array.length lhs then [| |] else
          Array.sub lhs (ci + 1) (Array.length lhs - (ci + 1)) in
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
         let postfix = if (ci + 1) >= Array.length lhs then [| |] else
             Array.sub lhs (ci + 1) (Array.length lhs - (ci + 1)) in
         { rul with lhs = Array.append (Array.sub lhs 0 ci) postfix  }
      | _                -> assert false) filtered
end

module Cm = ClauseMat

(** {b Note} The compiling step creates a tree ready to be used for pattern
    matching.  A tree guides the pattern matching by
    + accepting constructors and filtering possible rules,
    + getting the most efficient term to match in the stack,
    + storing terms from the stack that might be used in the right hand side,
      because they match a pattern variable {!constructor:Patt} in the
      {!field:lhs}.

    The first bullet is ensured using {!val:specialize}, {!val:default} and
    {!val:abstract} which allow to create new branches.

    Efficiency is managed thanks to heuristics, which are not yet
    implemented.

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
    rule can use, that are the terms {b that have been inspected}.  There
    may remain terms that haven't been inspected (because they are not needed
    to decide which rule to apply), but that are nevertheless needed in the
    {!field:rhs}.  Note that the {!field:Cm.var_catalogue} contains useless
    variables as well: these may have been needed by other rules, when several
    rules were still candidates.  The {!val:env_builder} is then initialized
    and contains only essential terms from the catalogue for the rule to
    apply.  The remaining variables, which will remain in the input stack will
    be fetched thanks to a subtree built by {!val:fetch}. *)

(** [split a] is {!val:List.split}[Array.to_list a]. *)
let split : ('a * 'b) array -> ('a list) * ('b list) =
  Array.fold_left (fun (accl, accr) (el, er) -> (el :: accl, er :: accr))
    ([], [])

(** [fetch l d e r] consumes [l] until environment build [e] contains as many
    elements as the number of variables in [r].  The environment builder [e] is
    also enriched.  The tree which allows this consumption is returned, with a
    leaf holding action [r] and the new environment.  Even though only
    essential terms could be consumed using appropriate swaps; it costs less
    to consume linearly the stack than performing multiple swaps. *)
let fetch : Cm.component array -> int -> int IntMap.t -> action -> t =
  fun line depth env_builder rhs ->
    let terms = fst (split line) in
    let missing = Bindlib.mbinder_arity rhs - (IntMap.cardinal env_builder) in
    let defn = { swap = None ; store = false ; children = StrMap.empty
               ; abstspec = None ; default = None } in
    let rec loop telst added env_builder =
      if added = missing then Leaf(env_builder, rhs) else
      match telst with
      | []       -> assert false
      | te :: tl ->
         begin match te with
         | Patt(Some(i), _, _) ->
            let neb =  IntMap.add (depth + added) i env_builder in
            let child = loop tl (succ added) neb in
            Node({ defn with store = true ; default = Some(child) })
         | Appl(_, _)          ->
            let s, args = Basics.get_args te in
            let newtl = s :: args @ tl in
            let child = loop newtl added env_builder in
            Node({ defn with default = Some(child) })
         | Abst(_, b)          ->
            let _, body = Bindlib.unbind b in
            let child = loop (body :: tl) added env_builder in
            Node( {defn with default = Some(child) })
         | Patt(None, _, _)
         | Symb(_, _)
         | Vari(_)             ->
            let child = loop tl added env_builder in
            Node({ defn with default = Some(child) })
         | _                   -> assert false
         end in
    loop terms 0 env_builder

(** [compile m] returns the decision tree allowing to parse efficiently the
    pattern matching problem contained in pattern matrix [m]. *)
let compile : Cm.t -> t = fun patterns ->
  (* let varcount = ref 0 in *)
  let rec compile patterns =
    let { Cm.var_catalogue = vcat ; _ } = patterns in
    (* Cm.pp Format.std_formatter patterns ; *)
    if Cm.is_empty patterns then
      begin
        failwith "matching failure" ; (* For debugging purposes *)
    (* Fail *)
      end
    else
      if Cm.exhausted patterns then
      (* A rule can be applied *)
        let { Cm.rhs ; Cm.lhs ; Cm.variables = pos2slot } = Cm.yield patterns in
        let f (count, map) tpos =
          let opslot = SubMap.find_opt tpos pos2slot in
          match opslot with
          | None     -> succ count, map
        (* ^ Discard useless variables *)
          | Some(sl) -> succ count, IntMap.add count sl map in
      (* [env_builder] maps future position in the term store to the slot in
         the environment. *)
        let _, env_builder = List.fold_left f (0, IntMap.empty)
          (List.rev vcat) in
      (* ^ For now, [env_builder] contains only the variables encountered
         while choosing the rule.  Other pattern variables needed in the rhs,
         which are still in the [lhs] will now be fetched. *)
        assert (IntMap.cardinal env_builder <=
                  Basics.SubtMap.cardinal pos2slot) ;
        let depth = List.length vcat in
        fetch lhs depth env_builder rhs
      else
        (* Set appropriate column as first*)
        let kept_cols = Cm.discard_cons_free patterns in
        let sel_in_partial = Cm.pick_best_among patterns kept_cols in
        let absolute_cind = kept_cols.(sel_in_partial) in
        let swap = if absolute_cind = 0 then None else Some(absolute_cind) in
        (* Extract this column *)
        let col = Cm.get_col absolute_cind patterns in
        let terms, _ = List.split col in
        let store = Cm.in_rhs terms in
        (* Get new var catalogue *)
        let newcat =
          let newvars = Cm.varpos patterns absolute_cind in
          newvars @ patterns.Cm.var_catalogue in
        (* Specializations *)
        let spepatts =
          let cons = Cm.get_cons terms in
          let f acc cons =
            let crepr = symrepr_of_term cons in
            let rules = Cm.specialize cons absolute_cind patterns.clauses in
            let ncm = { Cm.clauses = rules ; Cm.var_catalogue = newcat } in
            StrMap.add crepr ncm acc in
          List.fold_left f StrMap.empty cons in
        let children = StrMap.map compile spepatts in
        (* Default *)
        let defmat =
          let rules = Cm.default absolute_cind patterns.Cm.clauses in
          let ncm = { Cm.clauses = rules ; Cm.var_catalogue = newcat } in
          if Cm.is_empty ncm then None else Some(compile ncm) in
        Node({ swap = swap ; store = store ; children = children
             ; abstspec = None ; default = defmat }) in
  compile patterns
