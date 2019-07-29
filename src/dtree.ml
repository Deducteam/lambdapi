(** This module provides functions to compile rewrite rules to decision trees
    in order to pattern match the rules efficiently.  The method is based on
    Luc Maranget's {i Compiling Pattern Matching to Good Decision Trees},
    {{:10.1145/1411304.1411311}DOI}. *)
open Terms
open Extra
open Basics
open Treecstr
open Tree_types

(** Priority on topmost rule if set to true. *)
let rule_order : bool ref = ref false

(** [write_trees] contains whether trees created for rule parsing should be
    written to disk. *)
let write_trees : bool Pervasives.ref = Pervasives.ref false

(** Type of the leaves of the tree.  See {!module:Terms}, {!field:rhs}. *)
type action = (term_env, term) Bindlib.mbinder

(** See {!type:tree} in {!module:Terms}. *)
type t = (term, action) tree

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
end

(** Alternatives to a list based implementation would be cat-enable
    lists/deques, finger trees, random access lists.  One might want to look
    at
    - Okasaki, 1996, {i Purely Functional Data Structures},
    - Paterson and Hinze, {i Finger trees: a simple general purpose data
      structure}. *)

module ReductionStack = RedListStack

(** {3 Graphviz output} *)

(** Printing hint for conversion to graphviz. *)
type dot_term =
  | DotDefa (* Default case *)
  | DotAbst of tvar
  | DotCons of treecons
  | DotSuccess
  | DotFailure

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
  F.fprintf ppf "graph {@[<v>";
  let pp_dotterm : dot_term pp = fun oc dh -> match dh with
    | DotAbst(v) -> F.fprintf oc "λ%a" Print.pp_tvar v
    | DotDefa    -> F.fprintf oc "*"
    | DotCons(Symb(t)) -> F.fprintf oc "%s<sub>%d</sub>" t.c_sym t.c_ari
    | DotCons(Vari(s)) -> F.fprintf oc "%s" s
    | DotCons(Abst)    -> assert false
    | DotSuccess -> F.fprintf oc "✓"
    | DotFailure -> F.fprintf oc "✗"
  in
  let pp_tcstr : term tree_constraint pp = fun oc -> function
    | TcstrEq(i, j)        -> F.fprintf oc "@%d≡<sub>v</sub>@%d" i j
    | TcstrFreeVars(vs, i) ->
        F.fprintf oc "%a@@<sub>v</sub>%d" (F.pp_print_list P.pp_tvar)
          (Array.to_list vs) i
  in
  (* [write_tree n u v] writes tree [v] obtained from tree number [n] with a
     switch on [u] ({!constructor:None} if default). *)
  let rec write_tree : int -> dot_term -> t -> unit = fun father_l swon ->
    function
    | Leaf(_, a)       ->
        incr nodecount;
        let _, acte = Bindlib.unmbind a in
        F.fprintf ppf "@ %d [label=\"%a\"];" !nodecount P.pp acte;
        F.fprintf ppf "@ %d -- %d [label=<%a>];"
          father_l !nodecount pp_dotterm swon
    | Node(ndata)      ->
        let { swap ; children ; store ; abstraction ; default } = ndata in
        incr nodecount;
        let tag = !nodecount in
        (* Create node *)
        F.fprintf ppf "@ %d [label=\"@%d\"%s];"
          tag swap (if store then " shape=\"box\"" else "");
        (* Create edge *)
        F.fprintf ppf "@ %d -- %d [label=<%a>];"
          father_l tag pp_dotterm swon;
        TcMap.iter (fun s e -> write_tree tag (DotCons(s)) e) children;
        Option.iter (fun (v, t) -> write_tree tag (DotAbst(v)) t)
          abstraction;
        Option.iter (write_tree tag DotDefa) default;
    | Condition(cdata) ->
        let { ok ; condition ; fail } = cdata in
        incr nodecount;
        let tag = !nodecount in
        F.fprintf ppf "@ %d [label=<%a> shape=\"diamond\"];"
          tag pp_tcstr condition;
        F.fprintf ppf "@ %d -- %d [label=<%a>];"
          father_l tag pp_dotterm swon;
        write_tree tag DotSuccess ok;
        write_tree tag DotFailure fail
    | Fail             ->
        incr nodecount;
        F.fprintf ppf "@ %d [label=<!>];" !nodecount;
        F.fprintf ppf "@ %d -- %d [label=\"!\"];" father_l !nodecount
  in
  begin match tree with
  (* First step must be done to avoid drawing a top node. *)
  | Node({ swap ; store ; children;
           default ; abstraction }) ->
      F.fprintf ppf "@ 0 [label=\"@%d\"%s];"
        swap (if store then " shape=\"box\"" else "");
      TcMap.iter (fun sw c -> write_tree 0 (DotCons(sw)) c) children;
      Option.iter (fun (v, t) -> write_tree 0 (DotAbst(v)) t) abstraction;
      Option.iter (fun t -> write_tree 0 DotDefa t) default
  | Leaf(_)                         -> ()
  | _                               -> assert false
  end;
  F.fprintf ppf "@.}@\n@?";
  close_out ochan

(** {3 Binary constraints nodes} *)

(** A helper type to process [choose] results uniformly. *)
type bin_cstr = Fv of FvScorable.cstr
              | Nl of NlScorable.cstr
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

  (** Reduction stack containing the position of the subterm and the number of
      abstractions traversed at this position. *)
  type occur_rs = (Occur.t * int) ReductionStack.t

  (** Data needed to bind terms from the lhs into the rhs. *)
  type binding_data = term Tree_types.binding_data

  (** A redefinition of the rule type.

      {b Note} that {!type:array} is used while {!module:ReductionStack} could
      be used because {!val:pick_best_among} goes through all items of a rule
      anyway ([max(S) = Θ(|S|)]).  Since heuristics need to access elements of
      the matrix, we favour quick access with {!type:array}. *)
  type clause =
    { lhs : term array
    (** Left hand side of a rule.   *)
    ; rhs : action
    (** Right hand side of a rule. *)
    ; env_builder : (int * binding_data) list
    (** Maps slots of the {!val:vars} array to a slot of the final
        environment used to build the {!field:rhs}. *)
    ; nonlin : NlScorable.t
    (** Non linearity constraints attached to this rule. *)
    ; freevars : FvScorable.t
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
    | NlConstrain of NlScorable.cstr
    (** [NlConstrain(c, s)] indicates a non-linearity constraint on column [c]
        regarding slot [s]. *)
    | FvConstrain of FvScorable.cstr
    (** Free variables constraint: the term matched must contain {e at most} a
        specified set of variables. *)

  (** [pp o m] prints matrix [m] to out channel [o]. *)
  let pp : t pp = fun oc { clauses ; positions ; _ } ->
    let module F = Format in
    let pp_line oc { lhs ; freevars ; nonlin ; _ } =
      F.fprintf oc "@[<v>@[%a@]@,@[%a@]@,@[%a@]@]"
        (F.pp_print_list ~pp_sep:(Format.pp_print_space) Print.pp)
        (Array.to_list lhs)
        FvScorable.pp freevars
        NlScorable.pp nonlin in
    F.fprintf oc "Positions @@ @[<h>" ;
    F.pp_print_list ~pp_sep:(fun oc () -> F.fprintf oc ";") Occur.pp oc
      (ReductionStack.to_list positions |> List.map fst) ;
    F.fprintf oc "@] -- " ;
    F.fprintf oc "Depth: @[<h>" ;
    F.pp_print_list ~pp_sep:(fun oc () -> F.fprintf oc ";") F.pp_print_int oc
      (ReductionStack.to_list positions |> List.map snd) ;
    F.fprintf oc "@]@,";
    F.fprintf oc "{@[<v>@," ;
    F.pp_print_list ~pp_sep:F.pp_print_cut pp_line oc clauses ;
    F.fprintf oc "@.@]}"

  (** [of_rules r] creates the initial pattern matrix from a list of rewriting
      rules. *)
  let of_rules : rule list -> t = fun rs ->
    let r2r r =
      let lhs = Array.of_list r.Terms.lhs in
      let nonlin = NlScorable.empty in
      let freevars = FvScorable.empty in
      { lhs ; rhs = r.Terms.rhs ; nonlin ; freevars ; env_builder = [] }
    in
    let size = (* Get length of longest rule *)
      if rs = [] then 0 else
      List.max ~cmp:Int.compare
        (List.map (fun r -> List.length r.Terms.lhs) rs) in
    let positions = Occur.args_of size Occur.empty
                    |> List.map (fun x -> (x, 0))
                    |> ReductionStack.of_list
    in
    (* [|>] is reverse application, can be thought of as a Unix pipe | *)
    { clauses = List.map r2r rs ; slot = 0 ; positions }

  (** [is_empty m] returns whether matrix [m] is empty. *)
  let is_empty : t -> bool = fun m -> m.clauses = []

  (** [get_col n m] retrieves column [n] of matrix [m]. *)
  let get_col : int -> t -> term list = fun ind { clauses ; _ } ->
    List.map (fun { lhs ; _ } -> lhs.(ind)) clauses

  (** [score c] returns the score heuristic for column [c].  The score is a
      tuple containing the number of constructors and the number of storage
      required. *)
  let score : term list -> float = fun ts ->
    let rec loop ((ncons, nst) as acc) = function
      | []                 -> acc
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
      among columns [c] according to a heuristic, along with the score. *)
  let pick_best_among : t -> int array -> int * float = fun mat columns->
    let scores = Array.map (fun ci -> score (get_col ci mat)) columns in
    let index = Array.max_index ~cmp:(Pervasives.compare) scores in
    (index, scores.(index))

  (** [can_switch_on r k] returns whether a switch can be carried out on
      column [k] of clauses [r]. *)
  let can_switch_on : clause list -> int -> bool = fun  clauses k ->
    List.for_all (fun r -> Array.length r.lhs >= k + 1) clauses &&
    List.exists (fun r -> is_treecons r.lhs.(k)) clauses

  (** [discard_cons_free r] returns the list of indexes of columns containing
      terms that can be matched against (discard constructor-free columns) in
      clauses [r]. *)
  let discard_cons_free : clause list -> int array = fun clauses ->
    let ncols = List.max ~cmp:Int.compare
        (List.map (fun { lhs ; _ } -> Array.length lhs) clauses)
    in
    let switchable = List.init ncols (can_switch_on clauses) in
    let switchable2ind i e = if e then Some(i) else None in
    switchable |> List.filteri_map switchable2ind |> Array.of_list

  (** [choose m] returns the index of column to switch on. *)
  let choose : t -> (int * float) option = fun m ->
    let kept = discard_cons_free m.clauses in
    if kept = [||] then None else
    let sel_partial, score = pick_best_among m kept in
    let cind = kept.(sel_partial) in
    Some(cind, score)

  (** [is_exhausted p r] returns whether [r] can be applied or not, with [p]
      the occurrences of the terms in [r]. *)
  let is_exhausted : occur_rs -> clause -> bool =
    fun positions { lhs ; nonlin ; freevars ; _ } ->
    let nonl lhs =
      (* Verify that there are no non linearity constraints in the remaining
         terms.  We must check that there are no constraints in the remaining
         terms and no constraints left partially instantiated. *)
      let slots = Array.to_list lhs
                 |> List.filter_map
                      (function Patt(io, _, _) -> io | _ -> None) in
      let slots_uniq = List.sort_uniq Int.compare slots in
      List.same_length slots slots_uniq
      && not @@ List.exists (fun s -> NlScorable.constrained s nonlin)
        slots_uniq
    in
    let depths = ReductionStack.to_list positions |> List.map snd
                 |> Array.of_list
    in
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
    NlScorable.is_empty nonlin && FvScorable.is_empty freevars
    && (lhs = [||] || ripe lhs)

  (** [yield m] yields a clause to be applied. *)
  let yield : t -> decision = fun ({ clauses ; positions ; _ } as m) ->
    try
      if !rule_order
      then let fc = List.hd clauses in
        if is_exhausted positions fc then Yield(fc) else raise Not_found
      else let r = List.find (is_exhausted positions) clauses in
      Yield(r)
    with Not_found ->
      let nlcstrs = List.map (fun r -> r.nonlin) m.clauses in
      let rnl = match NlScorable.choose nlcstrs with
        | Some(c, i) -> (Nl(c), i)
        | None       -> (Unavailable, 0.)
      in
      let fvcstrs = List.map (fun r -> r.freevars) m.clauses in
      let rfv = match FvScorable.choose fvcstrs with
        | Some(c, i) -> (Fv(c), i)
        | None       -> (Unavailable, 0.)
      in
      let rs = match choose m with
        | None       -> (Unavailable, 0.)
        | Some(c, i) -> (Sp(c), i)
      in
      let r = [| rnl ; rfv ; rs |] in
      let best =
        if Array.for_all (fun (x, _) -> x = Unavailable) r then
          (Unavailable, 0.) else
          Array.max ~cmp:(fun (_, x) (_, y) -> Pervasives.compare x y) r
      in
      match fst best with
      | Nl(c)          -> NlConstrain(c)
      | Fv(c)          -> FvConstrain(c)
      | Sp(c)          -> Specialise(c)
      | Unavailable    -> Specialise(0)

  (** [get_cons l] extracts, sorts and uniqify terms that are tree
      constructors in [l].  The actual tree constructor (of type
      {!type:treecons}) is returned along the original term. *)
  let get_cons : term list -> (treecons * term) list = fun telst ->
    let keep_treecons e =
      let h, _, arity = get_args_len e in
      match h with
      | Symb({ sym_name ; sym_path ; _ }, _) ->
          Some(Symb({ c_mod = sym_path ; c_sym = sym_name
                    ; c_ari = arity }), e)
      | Abst(_, _)                           -> Some(Abst, e)
      | Vari(x)                              ->
          Some(Vari(Bindlib.name_of x), e)
      | _                                    -> None
    in
    let tc_fst_cmp (tca, _) (tcb, _) = tc_compare tca tcb in
    List.filter_map keep_treecons telst |> List.sort_uniq tc_fst_cmp

  (** [store m c d] returns whether the inspected term on column [c] of matrix
      [m] needs to be stored during evaluation. *)
  let store : t -> int -> bool = fun cm ci ->
    let _, (_, de), _ = ReductionStack.destruct cm.positions ci in
    let st_r r =
      match r.lhs.(ci) with
      | Patt(Some(_), _, _) -> true
      | Patt(_, _, e)       -> Array.length e < de
      | _                   -> false
    in
    List.exists st_r cm.clauses

  (** [update_aux c v r] returns clause [r] with auxiliary data updated
      (i.e. non linearity constraints and environment builder) when inspecting
      column [c] having met [v] vars until now. *)
  let update_aux : int -> int -> occur_rs -> clause -> clause =
    fun ci slot pos r ->
    let _, (_, depth), _ = ReductionStack.destruct pos ci in
    let t = r.lhs.(ci) in
    match fst (get_args t) with
    | Patt(i, _, e) ->
        let freevars = if (Array.length e) <> depth
          then FvScorable.instantiate slot
              (Array.map to_tvar e)
              r.freevars
          else r.freevars
        in
        let nonlin =
          match i with
          | Some(i) -> NlScorable.instantiate slot i r.nonlin
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
      let l, m, r = ReductionStack.destruct pos ci in
      let occ, depth = m in
      let _, _, nargs = get_args_len pat in
      let replace = Occur.args_of nargs occ
                    |> List.map (fun x -> (x, depth))
      in
      ReductionStack.restruct l replace r in
    let ph, pargs, lenp = get_args_len pat in
    let insert r e = Array.concat [ Array.sub r.lhs 0 ci
                                  ; e
                                  ; Array.drop (ci + 1) r.lhs ]
    in
    let filtrans r =
      let insert = insert r in
      let h, args, lenh = get_args_len r.lhs.(ci) in
      match ph, h with
      | Symb(_, _), Symb(_, _)
      | Vari(_)   , Vari(_)       ->
          if lenh = lenp && Basics.eq ph h
          then Some({r with lhs = insert (Array.of_list args)})
          else None
      | _         , Patt(_, _, _) ->
          let arity = List.length pargs in
          let e = Array.make arity (Patt(None, "", [||])) in
          Some({ r with lhs = insert e })
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
      let l, _, r = ReductionStack.destruct pos ci in
      ReductionStack.restruct l [] r
    in
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

  (** [abstract c v p r] computes the clauses resulting from the
      specialisation by an abstraction.  Note that the pattern can't be an
      applied lambda since the lhs is in normal form. *)
  let abstract : int -> tvar -> occur_rs -> clause list ->
                 occur_rs * clause list =
    fun ci v pos clauses ->
    let l, (occ, depth), r = ReductionStack.destruct pos ci in
    let occ = Occur.sub occ in (* Position of term inside lambda. *)
    let pos = ReductionStack.restruct l [(occ, depth + 1)] r in
    let insert r e = [ Array.sub r.lhs 0 ci
                     ; [| e |]
                     ; Array.drop (ci + 1) r.lhs ]
    in
    let transf (r:clause) =
      let ph, pargs = get_args r.lhs.(ci) in
      match ph with
      | Abst(_, b)           ->
          assert (pargs = []) ; (* Patterns in β-normal form *)
          let b = Bindlib.subst b (mkfree v) in
          let lhs = Array.concat (insert r b) in
          Some({ r with lhs })
      | Patt(_, _, _) as pat ->
          let lhs = Array.concat (insert r pat) in
          Some({ r with lhs })
      | Symb(_, _) | Vari(_) -> None
      | _                    -> assert false
    in
    (pos, List.filter_map transf clauses)

  (** [nl_succeed c r] computes the clause list from [r] that verify a
      non-linearity constraint [c]. *)
  let nl_succeed : NlScorable.cstr -> clause list -> clause list = fun c ->
    let f r =
      let nonlin = NlScorable.remove c r.nonlin in
      { r with nonlin }
    in
    List.map f

  (** [nl_fail c r] computes the clauses not failing a non-linearity
      constraint [c] among clauses [r]. *)
  let nl_fail : NlScorable.cstr -> clause list -> clause list = fun c ->
    let f { nonlin ; _ } = not (NlScorable.is_instantiated c nonlin) in
    List.filter f

  (** [fv_suceed c r] computes the clauses from [r] that verify a free
      variables constraint [c]. *)
  let fv_succeed : FvScorable.cstr -> clause list -> clause list = fun c ->
    let f r =
      let freevars = FvScorable.remove c r.freevars in
      { r with freevars }
    in
    List.map f

  (** [fv_fail c r] computes the clauses not failing a free variable
      constraint [c] among clauses [r]. *)
  let fv_fail : FvScorable.cstr -> clause list -> clause list = fun c ->
    let f { freevars ; _ } = not (FvScorable.is_instantiated c freevars) in
    List.filter f
end

module Cm = ClauseMat

(** [harvest l r e s] exhausts linearly the stack composed only of pattern
    variables with no non linear constraints. *)
let harvest : term array -> action -> (int * Cm.binding_data) list -> int ->
  t = fun lhs rhs env_builder slot ->
  let default_node = { swap = 0 ; store = false ; children = TcMap.empty
                     ; abstraction = None ; default = None }
  in
  let rec loop lhs env_builder slot = match lhs with
    | []                        -> Leaf(env_builder, rhs)
    | Patt(Some(i), _, e) :: ts ->
        let env_builder = (slot, (i, Array.map to_tvar e)) :: env_builder in
        let slot = slot + 1 in
        let child = loop ts env_builder slot in
        Node { default_node with store = true ; default = Some(child) }
    | Patt(None, _, _) :: ts    ->
        let child = loop ts env_builder slot in
        Node { default_node with default = Some(child) }
    | _                         -> assert false in
  loop (Array.to_list lhs) env_builder slot

(** {b Note} The compiling step creates a tree ready to be used for pattern
    matching.  A tree guides the pattern matching by
    - accepting constructors and filtering possible clauses,
    - guiding the matching in order to carry out as few atomic matchings as
      possible by selecting the most appropriate term in the stack,
    - storing terms from the stack that might be used in the right hand side,
      because they match a pattern variable {!constructor:Patt} in the
      {!field:lhs}.

    The first bullet is ensured using {!val:specialize}, {!val:default} and
    {!val:abstract} which allow to create new branches.

    Efficiency is managed thanks to heuristics handled by the {!val:score}
    function.

    The last is managed by the {!val:env_builder} as follows.  The evaluation
    process used two arrays, one containing elements, as binders, to be
    injected in the {!field:rhs}, and another one to memorise terms filtered
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

(** [compile m] returns the decision tree allowing to parse efficiently the
    pattern matching problem contained in pattern matrix [m]. *)
let rec compile : Cm.t -> t =
  let varcount = ref 0 in
  fun ({ clauses ; positions ; slot } as patterns) ->
  if Cm.is_empty patterns then Fail
  else match Cm.yield patterns with
  | Yield({ Cm.rhs ; env_builder ; Cm.lhs ; _ }) ->
      if lhs = [||] then Leaf(env_builder, rhs) else
      harvest lhs rhs env_builder slot
  | NlConstrain(constr)                 ->
      let ok = let nclauses = Cm.nl_succeed constr clauses in
        compile { patterns with Cm.clauses = nclauses }
      in
      let fail = let nclauses = Cm.nl_fail constr clauses in
        compile {patterns with Cm.clauses = nclauses }
      in
      let vi, vj = NlScorable.export constr in
      let condition = TcstrEq(vi, vj) in
      Condition({ ok ; condition ; fail })
  | FvConstrain(constr)                 ->
      let ok = let clauses = Cm.fv_succeed constr clauses in
        compile { patterns with Cm.clauses }
      in
      let fail = let clauses = Cm.fv_fail constr clauses in
        compile { patterns with Cm.clauses }
      in
      let slot, vars = FvScorable.export constr in
      let condition = TcstrFreeVars(vars, slot) in
      Condition({ ok ; condition ; fail })
  | Specialise(swap)                    ->
      let store = Cm.store patterns swap in
      let updated = List.map (Cm.update_aux swap slot positions) clauses in
      let slot = if store then succ slot else slot in
      let cons = Cm.get_col swap patterns |> Cm.get_cons in
      (* Constructors specialisation *)
      let children =
        let f acc (tr_cons, te_cons) =
          if tr_cons = Abst then acc else
          let positions, clauses = Cm.specialize te_cons swap positions
              updated in
          let ncm = { Cm.clauses ; Cm.slot ; Cm.positions } in
          TcMap.add tr_cons (compile ncm) acc in
        List.fold_left f TcMap.empty cons
      in
      (* Default child *)
      let default =
        let positions, clauses = Cm.default swap positions updated in
        let ncm = { Cm.clauses ; Cm.slot ; Cm.positions } in
        if Cm.is_empty ncm then None else Some(compile ncm)
      in
      (* Abstraction specialisation*)
      let abstraction =
        if List.for_all (fun (x, _) -> x <> Abst) cons then None else
        let var = Bindlib.new_var mkfree ("tr" ^ (string_of_int !varcount)) in
        incr varcount ;
        let positions, clauses = Cm.abstract swap var positions updated in
        let ncm = { Cm.clauses ; Cm.slot ; Cm.positions } in
        Some(var, compile ncm)
      in
      Node({ swap ; store ; children ; abstraction ; default })

(** [update_dtree s] updates decision tree of symbol [s]. *)
let update_dtree : sym -> unit = fun symb ->
  let open Timed in
  match symb.sym_mode with
  | Defin
  | Injec ->
      let pama = lazy (ClauseMat.of_rules !(symb.sym_rules)) in
      let tree = lazy (compile @@ Lazy.force pama) in
      let capacity = lazy (Tree_types.capacity @@ Lazy.force tree) in
      symb.sym_tree := (capacity, tree) ;
      if Pervasives.(!write_trees) then
        ( Format.printf "Wrote %s.gv\n" (symb.sym_name)
        ; to_dot symb.sym_name (Lazy.force tree) )
  | _     -> ()
