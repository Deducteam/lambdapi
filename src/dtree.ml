(** This module provides functions to compile rewrite rules to decision trees
    in order to pattern match the rules efficiently.  The method is explained
    in Luc Maranget's {i Compiling Pattern Matching to Good Decision Trees},
    {{:10.1145/1411304.1411311}DOI}. *)
open Terms
open Extra

(** See {!type:tree} in {!module:Terms}. *)
type t = tree

(** Type of the leaves of the tree.  See {!file:terms.ml}, {!recfield:rhs}. *)
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
    {!const:Fail} on tree [t]. *)
let iter : do_leaf:(int IntMap.t -> action -> 'a) ->
  do_node:(int option -> bool -> (term * 'a) list -> 'a option -> 'a) ->
  fail:'a -> t -> 'a = fun ~do_leaf ~do_node ~fail t ->
  let rec loop = function
    | Leaf(pa, a)                      -> do_leaf pa a
    | Fail                             -> fail
    | Node({ swap ; store ; children ; default }) ->
       do_node swap store (List.map (fun (teo, c) -> (teo, loop c)) children)
         (Option.map loop default) in
  loop t

(** [to_dot f t] creates a dot graphviz file [f].gv for tree [t].  Each node
    of the tree embodies a pattern matrix.  The label on the node is the
    column index in the matrix on which the matching is performed to give
    birth to children nodes.  The label on the edge between a node and its
    child represents the term matched to generate the next pattern matrix (the
    one of the child node); and is therefore one of the terms in the column of
    the pattern matrix whose index is the label of the node.  The first [d]
    edge is due to the initialization matrix (with {!recfield:origin} [=]
    {!cons:Init}). *)
let to_dot : string -> t -> unit = fun fname tree ->
  let module F = Format in
  let module P = Print in
  let ochan = open_out (fname ^ ".gv") in
  let ppf = F.formatter_of_out_channel ochan in
  let nodecount = ref 0 in
  F.fprintf ppf "graph {@[<v>" ;
  let pp_opterm : term option pp = fun oc teo -> match teo with
    | Some(t) -> P.pp oc t
    | None    -> F.fprintf oc "*" in
  (* [write_tree n u v] writes tree [v] obtained from tree number [n] with a
     switch on [u] ({!cons:None} if default). *)
  let rec write_tree : int -> term option -> t -> unit =
    fun father_l swon tree ->
    match tree with
    | Leaf(_, a) ->
      incr nodecount ;
      F.fprintf ppf "@ %d [label=\"" !nodecount ;
      let _, acte = Bindlib.unmbind a in
      P.pp ppf acte ; F.fprintf ppf "\"]" ;
      F.fprintf ppf "@ %d -- %d [label=\"" father_l !nodecount ;
      pp_opterm ppf swon ; F.fprintf ppf "\"];"
    | Node(ndata)   ->
      let { swap ; children ; store ; default } = ndata in
      incr nodecount ;
      let tag = !nodecount in
      begin (* Create node *)
        F.fprintf ppf "@ %d [label=\"" tag ;
        F.fprintf ppf "%d" (match swap with None -> 0 | Some(i) -> i) ;
        F.fprintf ppf "\"" ;
        if store then F.fprintf ppf " shape=\"box\"" ;
        F.fprintf ppf "]"
      end ;
      begin (* Create edge *)
        F.fprintf ppf "@ %d -- %d [label=\"" father_l tag ;
        pp_opterm ppf swon ; F.fprintf ppf "\"];"
      end ;
      List.iter (fun (s, e) -> write_tree tag (Some(s)) e) children ;
      (match default with None -> () | Some(tr) -> write_tree tag None tr)
    | Fail          ->
      incr nodecount ;
      F.fprintf ppf "@ %d -- %d [label=\"%s\"];" father_l !nodecount "!"
  in
  begin
    match tree with
    (* First step must be done to avoid drawing a top node. *)
    | Node({ swap ; children = ch ; store ; default }) ->
       F.fprintf ppf "@ 0 [label=\"%d\""
         (match swap with None -> 0 | Some(i) -> i) ;
       if store then F.fprintf ppf " shape=\"box\"" ;
       F.fprintf ppf "]" ;
       List.iter (fun (sw, c) -> write_tree 0 (Some(sw)) c) ch ;
       (match default with None -> () | Some(tr) -> write_tree 0 None tr)
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
  (** Type used to describe a line of a matrix (either a column or a row). *)
  type line = (term * Basics.Subterm.t) list

  (** A redefinition of the rule type. *)
  type rule = { lhs : line
              (** Left hand side of a rule. *)
              ; rhs : action
              (** Right hand side of a rule. *)
              ; variables : int Basics.SubtMap.t
              (** Mapping from positions of variable subterms in [lhs] to a
                  slot in a term env. *)}

  (** The core data, contains the rewrite rules. *)
  type matrix = rule list

  (** Type of a matrix of patterns.  Each line is a row having an attached
      action. *)
  type t = { values : matrix
           (** The rules. *)
           ; var_catalogue : Basics.Subterm.t list
           (** Contains positions of terms in {!recfield:lhs} that can be used
               as variables in any of the {!recfield:rhs} which appeared in
               the matrix that gave birth to this one. *)}

  (** [pp_line o l] prints line [l] to out channel [o]. *)
  let pp_line : line pp = fun oc l -> List.pp Print.pp ";" oc
    (List.map (fst) l)

  (** [pp o m] prints matrix [m] to out channel [o]. *)
  let pp : t pp = fun oc { values ; _ } ->
    let module F = Format in
    F.fprintf oc "[|@[<v>@," ;
    List.pp pp_line "\n  " oc (List.map (fun { lhs = l ; _ } -> l) values) ;
    (* List.pp does not process Format "@" directives when in sep *)
    F.fprintf oc "@.|]@,@?"

  (** [pos_needed_by l] returns a mapping from position of variables into [l]
      to the slot assigned to each variable in a {!type:term_env}. *)
  let pos_needed_by : line -> action -> int Basics.SubtMap.t = fun lhs rhs ->
    let module St = Basics.Subterm in
    let module StMap = Basics.SubtMap in
    let nvars = Bindlib.mbinder_arity rhs in
    let rec loop found st po =
      if found = nvars then StMap.empty else
      match st with
      | [] -> StMap.empty
      | x :: xs ->
         begin
           match x with
           | Patt(None, _, _)
           | Vari(_)
           | Symb(_, _)          -> loop found xs (St.succ po)
           | Patt(Some(i), _, _) -> StMap.add po i
              (loop (succ found) xs (St.succ po))
           | Appl(_, _) as x     -> let _, args = Basics.get_args x in
                                   deepen found args xs po
           | Abst(_, b)          -> let _, body = Bindlib.unbind b in
                                   deepen found [body] xs po
           | _                   -> assert false
         end
    and deepen found args remain po =
      let xpos = loop found args St.init in
      let nxpos = StMap.fold (fun xpo slot nmap ->
        StMap.add (St.prefix po xpo) slot nmap)
        StMap.empty xpos in
      StMap.union (fun _ _ -> assert false) nxpos
        (loop found remain (St.succ po))
    in
    (* Start as if the terms of the list were subterms of an initial term *)
    loop 0 (List.map fst lhs) (St.succ St.init)

  (** [of_rules r] creates the initial pattern matrix from a list of rewriting
      rules. *)
  let of_rules : Terms.rule list -> t = fun rs ->
    let r2r : Terms.rule -> rule = fun r ->
      let term_pos = Basics.Subterm.tag r.Terms.lhs in
      let variables = pos_needed_by term_pos r.Terms.rhs in
      { lhs = term_pos ; rhs = r.Terms.rhs
      ; variables = variables} in
    { values = List.map r2r rs ; var_catalogue = [] }

  (** [is_empty m] returns whether matrix [m] is empty. *)
  let is_empty : t -> bool = fun m -> m.values = []

  (** [get_col n m] retrieves column [n] of matrix [m].  There is some
      processing because all rows do not have the same length. *)
  let get_col : int -> t -> line = fun ind { values ; _ } ->
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
  let compare : line -> line -> int = fun _ _ -> 0

  (** [k @> l] is true if [k] is greater or equal than [l] in the sense of
      {!val:compare}. *)
  let (@>) : line -> line -> bool = fun l1 l2 -> compare l1 l2 >= 0

  (** [pick_best m] returns the index of the best column of matrix [m]
      according to a heuristic. *)
  let pick_best : t -> int = fun _ -> 0

  (** [is_pattern t] returns whether a term [t] is considered as a pattern *)
  let is_pattern : term -> bool = function
    | Patt(_, _, _) -> false
    | _             -> true

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

  (** [is_cons t] returns whether [t] can be considered as a constructor. *)
  let rec is_cons : term -> bool = function
    | Symb(_, _) | Abst(_, _) -> true
    | Appl(u, _)              -> is_cons u
    | _                       -> false

  (** [get_cons l] extracts a list of unique constructors from [l]. *)
  let get_cons : term list -> term list = fun telst ->
  (* membership of terms *)
    let rec mem : term -> term list -> bool = fun te xs ->
      match xs with
      | []       -> false
      | hd :: tl ->
         let s = fst (Basics.get_args hd) in
         if Basics.eq s te then true else mem te tl in
    let rec loop : 'a list -> 'a list -> 'a list = fun seen notseen ->
      match notseen with
      | [] -> List.rev seen
      | hd :: tl ->
         let s = fst (Basics.get_args hd) in
         loop (if mem s seen then seen else hd :: seen) tl in
    loop [] (List.filter is_cons telst)


  (** [update_catalogue c r] adds the position of the head of [r] to catalogue
      [c] if it is a pattern variable. *)
  (* XXX uniqueness of positions in catalogue?*)
  let update_catalogue : Basics.Subterm.t list -> rule ->
    Basics.Subterm.t list = fun varstack rule ->
      let { lhs ; _ } = rule in
      match List.hd lhs with
      | Patt(Some(_), _, _), p -> p :: varstack
      | _                      -> varstack
end

module Pm = Pattmat

(** [spec_filter p l] returns whether a line [l] (of a pattern matrix) must be
    kept when specializing the matrix on pattern [p]. *)
let rec spec_filter : term -> term -> bool = fun pat hd ->
  match pat, hd with
  | _            , Patt(None, _, _)    -> true
  (* ^ Wildcard or linear var not appearing in rhs *)
  | _            , Patt(Some(_), _, _) -> true
  (* ^ Linear var appearing in rhs *)
  | Symb(s, _)   , Symb(s', _)         -> s == s'
  | Appl(u1, u2) , Appl(v1, v2)        ->
    spec_filter u1 v1 && spec_filter u2 v2
  (* ^ Verify there are as many Appl (same arity of leftmost terms). *)
  | Abst(_, b1)  , Abst(_, b2)             ->
    let _, u, v = Bindlib.unbind2 b1 b2 in
    spec_filter u v
  | Vari(x)      , Vari(y)             -> Bindlib.eq_vars x y
  | Patt(_, _, e), _                   ->
  (* ^ Comes from a specialization on a lambda. *)
     let b = Bindlib.bind_mvar (Basics.to_tvars e) (lift hd) in
     Bindlib.is_closed b
  (* All below ought to be put in catch-all case*)
  | Symb(_, _), Abst(_, _)
  | Abst(_, _), Symb(_, _)
  | Symb(_, _), Appl(_, _)
  | Appl(_, _), Symb(_, _)
  | Appl(_, _), Abst(_, _)
  | Abst(_, _), Appl(_, _) -> false
  | _                      -> assert false

(** [spec_line p l] specializes the line [l] against pattern [p]. *)
let rec spec_line : term -> (term * Basics.Subterm.t) -> Pm.line = fun pat hd ->
  match hd with
  | Symb(_, _), _ -> []
  | Appl(u, v), p ->
  (* ^ Nested structure verified in filter *)
    let upat = fst @@ Basics.get_args pat in
    let np = Basics.Subterm.sub p in
    spec_line upat (u, np) @ [(v, Basics.Subterm.succ np)]
  | Abst(_, b), p ->
     let np = Basics.Subterm.sub p in
     let _, t = Bindlib.unbind b in [(t, np)]
  | Vari(_), _    -> []
  | _             -> (* Cases that require the pattern *)
  match hd, pat with
  | (Patt(_, _, [| |]), p), Appl(_, _) ->
      (* ^ Wildcard *)
     let arity = List.length @@ snd @@ Basics.get_args pat in
     let tagged = Basics.Subterm.tag
       (List.init arity (fun _ -> Patt(None, "", [| |]))) in
     (List.map (fun (te, po) -> (te, Basics.Subterm.prefix p po)) tagged)
  | (Patt(_, _, _), p)    , Abst(_, b) ->
     let _, t = Bindlib.unbind b in
     [(t, Basics.Subterm.prefix p Basics.Subterm.init)]
  | (Patt(_, _, _), _)    , _          -> []
  | _                                  -> assert false

(** [specialize p m] specializes the matrix [m] when matching against pattern
    [p].  A matrix can be specialized by a user defined symbol, an abstraction
    or a pattern variable.  The specialization always happen on the first
    column (which is swapped if needed).  We allow specialization by
    {!cons:Appl} as it allows to check the number of successive applications.
    In case an {!cons:Appl} is given as pattern [p], only terms having the
    same number of applications and having the same leftmost {e non}
    {!cons:Appl} are considered as constructors. *)
let specialize : term -> Pm.t -> Pm.t = fun p m ->
  (* Add the the variables that are consumed by the specialization *)
  let newstack = List.fold_left Pm.update_catalogue m.var_catalogue
    m.values in
  let filtered = List.filter (fun { Pm.lhs = l ; _ } ->
      spec_filter p (fst (List.hd l))) m.values in
  let newhds = List.map (fun rul -> spec_line p (List.hd rul.Pm.lhs))
    filtered in
  let newmat = List.map2 (fun newhd rul ->
    let oldlhstl = List.tl rul.Pm.lhs in
    { rul with Pm.lhs = newhd @ oldlhstl }) newhds filtered in
  { values = newmat ; var_catalogue = newstack }

(** [default m] computes the default matrix containing what remains to be
    matched if no specialization occurred. *)
let default : Pm.t -> Pm.t = fun { values = m ; var_catalogue = vs } ->
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
  let newst = List.fold_left Pm.update_catalogue vs m in
  { values = unfolded ; var_catalogue = newst }

(** {b Note} The compiling step creates a tree ready to be used for pattern
    matching.  A tree guides the pattern matching by
    + accepting constructors and filtering possible rules,
    + getting the most efficient term to match in the stack,
    + storing terms from the stack that might be used in the right hand side,
      because they match a pattern variable {!cons:Patt} in the
      {!recfield:lhs}.

    The first bullet is ensured using {!val:specialize} and {!val:default}
    which allow to create new branches.

    Efficiency is managed thanks to heuristics, which are not yet
    implemented.

    The last is managed by the {!val:env_builder} as follows.  The matching
    process uses, along with the tree, an array to store terms that may be
    used in the {!recfield:rhs}.  Terms are stores while parsing if the
    {!const:Node} as its {!recfield:store} as {!val:true}.  To know when to
    store variables, each rule is first parsed with {!val:Pm.pos_needed_by}
    to get the positions of {!const:Patt} in each {!recfield:lhs}.  Once these
    positions are known, the {!recfield:Pm.var_catalogue} can be built.  A
    {!recfield:Pm.var_catalogue} contains the accumulation of the positions
    encountered so far during successive specializations.  Once a rule can be
    triggered, {!recfield:Pm.var_catalogue} contains, in the order they appear
    during matching, all the variables to be used for the rule {b that has
    been inspected}.  There may remain terms that haven't been inspected
    (because they are not needed to decide which rule to apply), but that are
    nevertheless needed in the {!recfield:rhs}.  The
    {!recfield:Pm.var_catalogue} contains useless variables as well: these may
    have been needed by other rules, when several rules were still candidates.
    The {!val:env_builder} is then initialized with variables from the
    catalogue which are essential.  The remaining variables, which will remain
    in the input stack, are fetched with {!val:fetch}. *)

(** [fetch l d e r] consumes [l] until environment build [e] contains as many
    elements as the number of variables in [r].  The environment builder[e] is
    also enriched.  The tree which allows this consumption is returned, with a
    leaf holding action [r] and the new environment. *)
let fetch : Pm.line -> int -> int IntMap.t -> action -> t =
  fun line depth env_builder rhs ->
    let terms = fst (List.split line) in
    let missing = Bindlib.mbinder_arity rhs - (IntMap.cardinal env_builder) in
    let rec loop telst added env_builder =
      if added = missing then Leaf(env_builder, rhs) else
      match telst with
      | []       -> assert false
      | te :: tl ->
         begin
           match te with
           | Patt(Some(i), _, _) ->
              let neb =  IntMap.add (depth + added) i env_builder in
              let child = loop tl (succ added) neb in
              Node({ swap = None ; store = true ; children = []
                   ; default = Some(child) })
           | Appl(_, _) as a     ->
              let newtl = snd (Basics.get_args a) @ tl in
              let child = loop newtl added env_builder in
              Node({ swap = None ; store = false ; children = []
                   ; default = Some(child) })
           | Symb(_, _)          ->
              let child = loop tl added env_builder in
              Node({ swap = None ; store = false ; children = []
                   ; default = Some(child) })
           | Abst(_, b)          ->
              let _, body = Bindlib.unbind b in
              let child = loop (body :: tl) added env_builder in
              Node( {swap = None ; store = false ; children = []
                    ; default = Some(child) })
           | Patt(None, _, _)    ->
              let child = loop tl added env_builder in
              Node({ swap = None ; store = false ; children = []
                   ; default = Some(child) })
           | _                   -> assert false
         end in
    loop terms 0 env_builder

(** [compile m] returns the decision tree allowing to parse efficiently the
    pattern matching problem contained in pattern matrix [m]. *)
let rec compile : Pm.t -> t = fun patterns ->
  let { Pm.values = m ; Pm.var_catalogue = vcat } = patterns in
  if Pm.is_empty patterns then
    begin
      failwith "matching failure" ; (* For debugging purposes *)
      (* Dtree.Fail *)
    end
  else
    if Pm.exhausted (List.hd m) then
      (* A rule can be applied *)
      let rhs = (List.hd m).Pm.rhs in
      let lhs = (List.hd m).Pm.lhs in
      let pos2slot = (List.hd m).Pm.variables in
      (* [env_builder] maps future position in the term store to the slot in
         the environment. *)
      let env_builder = snd (List.fold_left (fun (i, m) tpos ->
        let opslot = Basics.SubtMap.find_opt tpos pos2slot in
        match opslot with
        | None     -> succ i, m
        (* ^ The stack may contain more variables than needed for the
           rule *)
        | Some(sl) -> succ i, IntMap.add i sl m)
                               (0, IntMap.empty) (List.rev vcat)) in
      (* ^ For now, [env_builder] contains only the variables encountered
         while choosing the rule.  Other pattern variables needed in the rhs,
         which are still in the [lhs] will now be fetched. *)
      let depth = List.length vcat in
      fetch lhs depth env_builder rhs
    else
      (* Pick a column in the matrix and pattern match on the constructors in
         it to grow the tree. *)
      let kept_cols = Pm.discard_patt_free patterns in
      let sel_in_partial = Pm.pick_best (Pm.select patterns kept_cols) in
      let swap = if kept_cols.(sel_in_partial) = 0 then None
        else Some kept_cols.(sel_in_partial) in
      let spm = match swap with
        | None    -> patterns
        | Some(i) -> Pm.swap patterns i in
      let fcol = Pm.get_col 0 spm in
      let store = (* Store if there is a pattern variable in fcol *)
        let rec loop : term list -> bool = function
          | []                       -> false
          | Patt(Some(_), _, _) :: _ -> true
          | _ :: xs                  -> loop xs in
        loop (List.map fst fcol) in
      let cons = Pm.get_cons (fst (List.split fcol)) in
      let spepatts = List.map (fun s ->
        (fst (Basics.get_args s), specialize s spm)) cons in
      let default = let dm = default spm in
                    if Pm.is_empty dm then None else Some(compile dm) in
      let children = List.map (fun (c, p) -> (c, compile p)) spepatts in
      Node({ swap = swap ; store = store ; children = children
           ; default = default })
