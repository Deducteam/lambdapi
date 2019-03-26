(** This module provides functions to compile rewrite rules to decision trees
    in order to pattern match the rules efficiently.  The method is explained
    in Luc Maranget's {i Compiling Pattern Matching to Good Decision Trees},
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

(** [depth t] computes the depth of tree [t]. *)
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
    of arguments. *)
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
    of the tree embodies a pattern matrix.  The label on the node is the
    column index in the matrix on which the matching is performed to give
    birth to children nodes.  The label on the edge between a node and its
    child represents the term matched to generate the next pattern matrix (the
    one of the child node); and is therefore one of the terms in the column of
    the pattern matrix whose index is the label of the node. *)
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

(** Pattern matrices is a way to encode a pattern matching problem.  A line is
    a candidate instance of the values matched.  Each line is a pattern having
    an action attached.  This module provides functions to operate on these
    matrices. *)
module Pattmat =
struct
  (** A component of the matrix *)
  type component = term * Basics.Subterm .t

  let pp_component : component pp = fun oc (te, pos) ->
    let module F = Format in
    F.fprintf oc "@[<h>%a@ %@@ %a@]" Print.pp te Basics.Subterm.pp pos

  (** A redefinition of the rule type. *)
  type rule = { lhs : component list
              (** Left hand side of a rule. *)
              ; rhs : action
              (** Right hand side of a rule. *)
              ; variables : int SubMap.t
              (** Mapping from positions of variable subterms in [lhs] to a
                  slot in a term env. *)}

  (** The core data, contains the rewrite rules. *)
  type matrix = rule list

  (** Type of a matrix of patterns.  Each line is a row having an attached
      action. *)
  type t = { values : matrix
           (** The rules. *)
           ; var_catalogue : Sub.t list
           (** Contains positions of terms in {!field:lhs} that can be used
               as variables in any of the {!field:rhs} which appeared in
               the matrix that gave birth to this one. *)}

  (** [pp o m] prints matrix [m] to out channel [o]. *)
  let pp : t pp = fun oc { values ; _ } ->
    let module F = Format in
    let pp_line oc l =
      F.fprintf oc "@[<h>" ;
      F.pp_print_list ~pp_sep:(fun _ () -> F.fprintf oc ";@ ")
        pp_component oc l ;
      F.fprintf oc "@]" in
    F.fprintf oc "{@[<v>@," ;
    F.pp_print_list ~pp_sep:F.pp_print_cut pp_line oc
      (List.map (fun { lhs ; _ } -> lhs) values) ;
    F.fprintf oc "@.}@,"

  (** [flushout_vars l] returns a mapping from position of variables into [l]
      to the slot assigned to each variable in a {!type:term_env}. *)
  let flushout_vars : component list -> action -> int SubMap.t = fun lhs rhs ->
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
           | Appl(_, _) as x     -> let _, args = Basics.get_args x in
                                   deepen found args xs po
           | Abst(_, b)          -> let _, body = Bindlib.unbind b in
                                   deepen found [body] xs po
           | _                   -> assert false
         end
    and deepen found args remain po =
      let xpos = loop found args Sub.init in
      let nxpos = SubMap.fold (fun xpo slot nmap ->
        SubMap.add (Sub.prefix po xpo) slot nmap)
        SubMap.empty xpos in
      SubMap.union (fun _ _ -> assert false) nxpos
        (loop found remain (Sub.succ po))
    in
    (* Start as if the terms of the list were subterms of an initial term *)
    loop 0 (List.map fst lhs) (Sub.succ Sub.init)

  (** [of_rules r] creates the initial pattern matrix from a list of rewriting
      rules. *)
  let of_rules : Terms.rule list -> t = fun rs ->
    let r2r : Terms.rule -> rule = fun r ->
      let term_pos = Basics.Subterm.tag r.Terms.lhs in
      let variables = flushout_vars term_pos r.Terms.rhs in
      { lhs = term_pos ; rhs = r.Terms.rhs
      ; variables = variables} in
    { values = List.map r2r rs ; var_catalogue = [] }

  (** [is_empty m] returns whether matrix [m] is empty. *)
  let is_empty : t -> bool = fun m -> m.values = []

  (** [get_col n m] retrieves column [n] of matrix [m].  There is some
      processing because all rows do not have the same length. *)
  let get_col : int -> t -> component list = fun ind { values ; _ } ->
    let opcol = List.fold_left (fun acc { lhs = li ; _ } ->
        List.nth_opt li ind :: acc) [] values in
    let rem = List.filter (function None -> false | Some(_) -> true) opcol in
    List.map (function Some(e) -> e | None -> assert false) rem

  (** [select m i] keeps the columns of [m] whose index are in [i]. *)
  let select : t -> int array -> t = fun m indexes ->
    { m with
      values = List.map (fun rul ->
        { rul with
          lhs = Array.fold_left (fun acc i -> List.nth rul.lhs i :: acc)
            [] indexes }) m.values }

  (** [swap p i] brings the [i]th column as 1st column. *)
  let swap : t -> int -> t = fun pm c ->
    { pm with values = List.map (fun rul ->
      { rul with lhs = List.bring c rul.lhs }) pm.values }

  (** [compare c d] compares columns [c] and [d] returning: a positive integer
      if [c > d], 0 if [c = d] or a negative integer if [c < d]; where [<],
      [=] and [>] are defined according to a heuristic.  *)
  let compare : component list -> component list -> int = fun _ _ -> 0

  (** [k @> l] is true if [k] is greater or equal than [l] in the sense of
      {!val:compare}. *)
  let (@>) : component list -> component list -> bool = fun l1 l2 ->
    compare l1 l2 >= 0

  (** [pick_best m] returns the index of the best column of matrix [m]
      according to a heuristic. *)
  let pick_best : t -> int = fun _ -> 0

  (** [is_pattern t] returns whether a term [t] is considered as a pattern. *)
  (* XXX = is_cons??? *)
  let rec is_pattern : term -> bool = function
    | Patt(_, _, _)   -> false
    | Appl(_, _) as a -> is_pattern (fst (Basics.get_args a))
    | _               -> true

  (** [exhausted r] returns whether rule [r] can be further pattern matched or
      if it is ready to yield the action.  A rule is exhausted when its left
      hand side is composed only of wildcards. *)
  let exhausted : rule -> bool = fun { lhs ; _ }->
    let rec loop = function
      | []                            -> true
      | (x, _) :: _ when is_pattern x -> false
      | _ :: xs                       -> loop xs in
    loop lhs

  (** [can_switch_on p k] returns whether a switch can be carried out on
      column [k] in matrix [p] *)
  let can_switch_on : t -> int -> bool = fun { values ; _ } k ->
    let rec loop : rule list -> bool = function
      | []      -> true
      | r :: rs ->
        begin
          match List.nth_opt r.lhs k with
          | None       -> loop rs
          | Some(t, _) -> is_pattern t
        end in
    loop values

  (** [discard_patt_free m] returns the list of indexes of columns containing
      terms that can be matched against (discard pattern-free columns). *)
  let discard_patt_free : t -> int array = fun m ->
    let ncols = List.extremum (>)
      (List.map (fun { lhs ; _ } -> List.length lhs) m.values) in
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
  (* [is_cons t] returns whether [t] can be considered as a constructor. *)
    let rec is_cons : term -> bool = function
      | Vari(_)
      | Symb(_, _)      -> true
      | Appl(_, _) as a -> let hd, _ = Basics.get_args a in is_cons hd
      | _               -> false in
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
  let varpos : t -> Sub.t list = fun pm ->
    let is_var (te, _) = match te with
      | Patt(Some(_), _, _) -> true
      | _                   -> false in
    let _, vars = List.split (List.filter is_var (get_col 0 pm)) in
    (* We do not care about keeping the order of the new variables in [vars]
       since for any rule, at most one of them will be chosen. *)
    List.sort_uniq Sub.compare vars
end

module Pm = Pattmat

(** [spec_filter p h] returns whether a line with head [h] (from a pattern
    matrix) must be kept when specializing the matrix on pattern [p]. *)
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

(** [spec_transform p h] transform head of line [h] when specializing against
    pattern [p]. *)
let rec spec_transform : term -> (term * Sub.t) -> Pm.component list = fun pat
  hd ->
  match hd with
  | Symb(_, _), _
  | Vari(_)   , _ -> []
  | Appl(_, _), p ->
  (* ^ Arguments verified in filter *)
    let upat = fst @@ Basics.get_args pat in
    let hs, hargs = Basics.get_args (fst hd) in
    let np = Sub.sub p in
    let tagged = Sub.tag ~empty:(Sub.succ np) hargs in
    spec_transform upat (hs, np) @ tagged
  | _             -> (* Cases that require the pattern *)
  match hd, pat with
  | (Patt(_, _, e), p), Appl(_, _) ->
     let arity = List.length @@ snd @@ Basics.get_args pat in
     let tagged = Sub.tag
       (List.init arity (fun _ -> Patt(None, "", e))) in
     (List.map (fun (te, po) -> (te, Sub.prefix p po)) tagged)
  | (Patt(_, _, _), _)    , _      -> []
  | _                              -> assert false

(** [specialize p m] specializes the matrix [m] when matching against pattern
    [p].  A matrix can be specialized by a user defined symbol, an abstraction
    or a pattern variable.  The specialization always happen on the first
    column (which is swapped if needed).  In case an {!constructor:Appl} is
    given as pattern [p], only terms having the same number of arguments and
    the same leftmost {e non} {!constructor:Appl} term match. *)
let specialize : term -> Pm.t -> Pm.t = fun p m ->
  let newvars = Pm.varpos m in
  let newcat = newvars @ m.var_catalogue in
  let filtered = List.filter (fun { Pm.lhs = l ; _ } ->
      spec_filter p (fst (List.hd l))) m.values in
  let newhds = List.map (fun rul -> spec_transform p (List.hd rul.Pm.lhs))
    filtered in
  let newmat = List.map2 (fun newhd rul ->
    let oldlhstl = List.tl rul.Pm.lhs in
    { rul with Pm.lhs = newhd @ oldlhstl }) newhds filtered in
  { values = newmat ; var_catalogue = newcat }

(** [abstract m] is a specialization on abstractions. *)
let abstract : tvar -> Pm.t -> Pm.t = fun free { values ; var_catalogue } ->
  (* Substitute all binders with the same variable *)
  let rec filt = function
    | Abst(_, _)
    | Patt(_, _, _)   -> true
    | Appl(_, _) as a ->
       filt (fst (Basics.get_args a))
    | _               -> false in
  let filtered = List.filter (fun { Pm.lhs ; _} -> filt (fst (List.hd lhs)))
    values in
  let rec transf = function
    | Abst(_, b), p        ->
       let np = Sub.sub p in
       let t = Bindlib.subst b (mkfree free) in [(t, np)]
    | Patt(s, n, e), p     ->
       let np = Sub.sub p in
       let nenv = Array.append e [| mkfree free |] in
       assert (Basics.distinct_vars nenv) ;
       [(Patt(s, n, nenv), np)]
    | Appl(_, _), _ as a_p ->
       let hd, args = Basics.get_args (fst a_p) in
       let np = Sub.sub (snd a_p) in
       let argtagged = Sub.tag ~empty:(Sub.succ np) args in
       (* ?empty might be wrong *)
       transf (hd, np) @ argtagged
    | _                    -> assert false in
  let newhds = List.map (fun { Pm.lhs ; _ } -> transf (List.hd lhs)) filtered in
  let unfolded = List.map2 (fun newhd rul ->
    let old_lhs_tl = List.tl rul.Pm.lhs in
    { rul with Pm.lhs = newhd @ old_lhs_tl}) newhds filtered in
  let newvars = Pm.varpos { values ; var_catalogue } in
  let newcat = newvars @ var_catalogue in
  { values = unfolded ; var_catalogue = newcat }

(** [default m] computes the default matrix containing what remains to be
    matched if no specialization occurred. *)
let default : Pm.t -> Pm.t = fun pm ->
  let { Pm.values = m ; Pm.var_catalogue = vcat ; _ } = pm in
  let filtered = List.filter (fun { Pm.lhs = l ; _ } ->
      match fst @@ List.hd l with
      | Patt(_ , _, _) -> true
      | Symb(_, _)
      | Abst(_, _)
      | Vari(_)
      | Appl(_, _)     -> false
      | _              -> assert false) m in
  let unfolded = List.map (fun rul ->
      match List.hd rul.Pm.lhs with
      | Patt(_, _, _), _ ->
        { rul with Pm.lhs = List.tl rul.Pm.lhs }
      | _             -> assert false) filtered in
  let newvars = Pm.varpos pm in
  let newcat = newvars @ vcat in
  { values = unfolded ; var_catalogue = newcat }

(** {b Note} The compiling step creates a tree ready to be used for pattern
    matching.  A tree guides the pattern matching by
    + accepting constructors and filtering possible rules,
    + getting the most efficient term to match in the stack,
    + storing terms from the stack that might be used in the right hand side,
      because they match a pattern variable {!constructor:Patt} in the
      {!field:lhs}.

    The first bullet is ensured using {!val:specialize} and {!val:default}
    which allow to create new branches.

    Efficiency is managed thanks to heuristics, which are not yet
    implemented.

    The last is managed by the {!val:env_builder} as follows.  The matching
    process uses, along with the tree, an array to store terms that may be
    used in the {!field:rhs}.  Terms are stored while parsing if the
    {!constructor:Node} has its {!field:store} at {!val:true}.  To know when
    to store variables, each rule is first parsed with {!val:Pm.pos_needed_by}
    to get the positions of {!constructor:Patt} in each {!field:lhs}.  Once
    these positions are known, the {!field:Pm.var_catalogue} can be built.  A
    {!field:Pm.var_catalogue} contains the accumulation of the positions
    encountered so far during successive specializations.  Once a rule can be
    triggered, {!field:Pm.var_catalogue} contains, in the order they appear
    during matching, all the variables the rule can use, that are the
    variables {b that has been inspected}.  There may remain terms that
    haven't been inspected (because they are not needed to decide which rule
    to apply), but that are nevertheless needed in the {!field:rhs}.  Note
    that the {!field:Pm.var_catalogue} contains useless variables as well:
    these may have been needed by other rules, when several rules were still
    candidates.  The {!val:env_builder} is then initialized with the essential
    variables from the catalogue.  The remaining variables, which will remain
    in the input stack, will be fetched thanks to a subtree built by
    {!val:fetch}. *)

(** [fetch l d e r] consumes [l] until environment build [e] contains as many
    elements as the number of variables in [r].  The environment builder[e] is
    also enriched.  The tree which allows this consumption is returned, with a
    leaf holding action [r] and the new environment. *)
let fetch : Pm.component list -> int -> int IntMap.t -> action -> t =
  fun line depth env_builder rhs ->
    let terms = fst (List.split line) in
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
         | Appl(_, _) as a     ->
            let newtl = snd (Basics.get_args a) @ tl in
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
let compile : Pm.t -> t = fun patterns ->
  let varcount = ref 0 in
  let rec compile patterns =
    let { Pm.values = m ; Pm.var_catalogue = vcat } = patterns in
    Pm.pp Format.std_formatter patterns ;
    if Pm.is_empty patterns then
      begin
        failwith "matching failure" ; (* For debugging purposes *)
    (* Fail *)
      end
    else
      if Pm.exhausted (List.hd m) then
      (* A rule can be applied *)
        let rhs = (List.hd m).Pm.rhs in
        let lhs = (List.hd m).Pm.lhs in
        let pos2slot = (List.hd m).Pm.variables in
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
        let kept_cols = Pm.discard_patt_free patterns in
        let sel_in_partial = Pm.pick_best (Pm.select patterns kept_cols) in
        let swap = if kept_cols.(sel_in_partial) = 0 then None
          else Some kept_cols.(sel_in_partial) in
        let spm = match swap with
          | None    -> patterns
          | Some(i) -> Pm.swap patterns i in
        (* Extract this column *)
        let fcol = Pm.get_col 0 spm in
        let f_terms, _ = List.split fcol in
        let store = Pm.in_rhs f_terms in
        (* Specializations *)
        let cons = Pm.get_cons f_terms in
        let spepatts = List.fold_left (fun acc cons ->
          StrMap.add (symrepr_of_term cons) (specialize cons spm) acc)
          StrMap.empty cons in
        let children = StrMap.map compile spepatts in
        (* Abstraction *)
        let abst = if Pm.contains_abst f_terms then
            let newfreevar =
              let suffix = string_of_int !varcount in
              Bindlib.new_var mkfree ("x" ^ suffix) in
            incr varcount ;
            let am = abstract newfreevar spm in
            if Pm.is_empty am then None else Some(newfreevar, compile am)
          else None in
        (* Default *)
        let default = let dm = default spm in
                      if Pm.is_empty dm then None else Some(compile dm) in
        Node({ swap = swap ; store = store ; children = children
             ; abstspec = abst ; default = default }) in
  compile patterns
