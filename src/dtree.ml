(** Compilation of rewriting rules to decision trees.

    This module handles the compilation of rewriting rules to “decision trees”
    based on the method described by Luc Maranget.

    @see <https://doi.org/10.1145/1411304.1411311> *)

open Timed
open Extra
open Terms
open Basics
open Treecstr
open Tree_types

(** Priority on topmost rule if set to true. *)
let rule_order : bool Pervasives.ref = Pervasives.ref false

(** Type of the leaves of the tree (see {!field:Terms.rhs}). *)
type action = (term_env, term) Bindlib.mbinder

(** See {!type:tree} in {!module:Terms}. *)
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

(** [is_treecons t] tells whether the term [t] corresponds to a constructor in
    the sense of the module {!module:Tree_types.TC}. *)
let is_treecons : term -> bool = fun t ->
  match fst (get_args t) with
  | Patt(_, _, _) -> false
  | Vari(_)
  | Abst(_, _)
  | Symb(_, _)    -> true
  | _             -> assert false

(** {3 Reduction substrate} *)

(** Data structure used to represent the stack of arguments during the pattern
    matching operation. *)
module Stack : sig
  (** Type of a substrate with elements of type ['a]. *)
  type 'a t

  (** The empty substrate. *)
  val empty : 'a t

  (** [is_empty v] tells whether a substrate is empty. *)
  val is_empty : 'a t -> bool

  (** [of_list l] returns a substrate containing the elements of [l]. *)
  val of_list : 'a list -> 'a t

  (** [to_list s] returns a list representing the substrate [s]. *)
  val to_list : 'a t -> 'a list

  (** [length s] gives the number of elements of the substrate [s]. *)
  val length : 'a t -> int

  (** Prefix of a substrate. *)
  type 'a prefix

  (** Suffix of a substrate. *)
  type 'a suffix

  (** [destruct s i] splits the substrate [s] into a triple [(l, m, r)], where
      [l] is the prefix of [s] up to its [i]-th element (excluded), [m] is the
      [i]-th element of [s], and [r] is the remaining suffix of [m].
      @raise Invalid_argument when [i < 0].
      @raise Not_found when [i ≥ length v]. *)
  val destruct : 'a t -> int -> 'a prefix * 'a * 'a suffix

  (** [restruct l m r] builds a substrate given a prefix [l], a middle list of
      element [m], and a suffix [r]. We will typically use [destruct] to get a
      triple [(l,e,r)], and then use [restruct l m r] where the list [m] comes
      from some operation applied on the element [e]. *)
  val restruct : 'a prefix -> 'a list -> 'a suffix -> 'a t
end = struct
  type 'a t = 'a list
  type 'a prefix = 'a list
  type 'a suffix = 'a list
  let empty = []
  let is_empty l = l = []
  external of_list : 'a list -> 'a t = "%identity"
  external to_list : 'a t -> 'a list = "%identity"
  let length = List.length

  let destruct e i =
    if i < 0 then invalid_arg "RedListStack.destruct" ;
    let rec destruct l i r =
      match (r, i) with
      | ([]  , _) -> raise Not_found
      | (v::r, 0) -> (l, v, r)
      | (v::r, i) -> destruct (v :: l) (i - 1) r
    in
    destruct [] i e

  let restruct l m r = List.rev_append l (m @ r)
end

(** {b NOTE} we ideally need the {!module:Stack} to provide fast access to any
    element in the substrate (for swaps) as well as fast {!val:Stack.destruct}
    and {!val:Stack.restruct} (to inspect a particular element, reduce it, and
    then reinsert it). In practice, the naive representation based on lists is
    faster than more elaborate solutions, unless there are rules with {e many}
    arguments. Alternatives to a list-based implementation would be cat-enable
    lists / deques, finger trees (Paterson & Hinze) or random access lists. In
    the current implementation, [destruct e i] has a time complexity of [Θ(i)]
    and [restruct l m r] has a time complexity of [Θ(length l + length m)]. *)

(** {3 Graphviz output} *)

(** Printing hint for conversion to graphviz. *)
type dot_term =
  | DotDefa (* Default case *)
  | DotAbst of tvar
  | DotCons of TC.t
  | DotSuccess
  | DotFailure

(** [to_dot f t] creates a dot graphviz file [f].gv for tree [t].  Each node
    of the tree embodies a pattern matrix.  The label of a node is the
    column index in the matrix on which the matching is performed to give
    birth to children nodes.  The label on the edge between a node and one of
    its children represents the term matched to generate the next pattern
    matrix (the one of the child node); and is therefore one of the terms in
    the column of the pattern matrix whose index is the label of the node. *)
let to_dot : string -> sym -> unit = fun fname s ->
  let output_tree : t pp = fun oc tree ->
    let pp_dotterm : dot_term pp = fun oc dh ->
      let out fmt = Format.fprintf oc fmt in
      match dh with
      | DotAbst(v)           -> out "λ%a" Print.pp_tvar v
      | DotDefa              -> out "*"
      | DotCons(Symb(a,n,_)) -> out "%s<sub>%d</sub>" n a
      | DotCons(Vari(s))     -> out "%s" s
      | DotCons(Abst)        -> assert false
      | DotSuccess           -> out "✓"
      | DotFailure           -> out "✗"
    in
    let pp_tcstr : term tree_constraint pp = fun oc cstr ->
      let out fmt = Format.fprintf oc fmt in
      let pp_ar oc ar =
        Format.pp_print_list Print.pp_tvar oc (Array.to_list ar)
      in
      match cstr with
      | Constr_Eq(i, j) -> out "@%d≡<sub>v</sub>@%d" i j
      | Constr_FV(vs,i) -> out "%a@@<sub>v</sub>%d" pp_ar vs i
    in
    let out fmt = Format.fprintf oc fmt in
    let node_count = ref 0 in
    (* [write_tree n u v] writes tree [v] obtained from tree number [n] with a
       switch on [u] ({!constructor:None} if default). *)
    let rec write_tree : int -> dot_term -> t -> unit = fun father_l swon t ->
      incr node_count;
      match t with
      | Leaf(_, a)  ->
          let _, acte = Bindlib.unmbind a in
          out "@ %d [label=\"%a\"];" !node_count Print.pp acte;
          out "@ %d -- %d [label=<%a>];" father_l !node_count pp_dotterm swon
      | Node({swap; children; store; abstraction=abs; default}) ->
          let tag = !node_count in
          (* Create node *)
          out "@ %d [label=\"@%d\"%s];" tag swap
            (if store then " shape=\"box\"" else "");
          (* Create edge *)
          out "@ %d -- %d [label=<%a>];" father_l tag pp_dotterm swon;
          TCMap.iter (fun s e -> write_tree tag (DotCons(s)) e) children;
          Option.iter (fun (v, t) -> write_tree tag (DotAbst(v)) t) abs;
          Option.iter (write_tree tag DotDefa) default
      | Cond({ ok ; cond ; fail }) ->
          let tag = !node_count in
          out "@ %d [label=<%a> shape=\"diamond\"];" tag pp_tcstr cond;
          out "@ %d -- %d [label=<%a>];" father_l tag pp_dotterm swon;
          write_tree tag DotSuccess ok;
          write_tree tag DotFailure fail
      | Fail        ->
          out "@ %d [label=<!>];" !node_count;
          out "@ %d -- %d [label=\"!\"];" father_l !node_count
    in
    out "graph {@[<v>";
    begin
      match tree with
      (* First step must be done to avoid drawing a top node. *)
      | Node({ swap ; store ; children; default ; abstraction }) ->
          out "@ 0 [label=\"@%d\"%s];" swap
            (if store then " shape=\"box\"" else "");
          TCMap.iter (fun sw c -> write_tree 0 (DotCons(sw)) c) children;
          Option.iter (fun (v, t) -> write_tree 0 (DotAbst(v)) t) abstraction;
          Option.iter (fun t -> write_tree 0 DotDefa t) default
      | Leaf(_) -> ()
      | _       -> assert false
    end;
    out "@.}@\n@?"
  in
  let tree = Lazy.force (snd !(s.sym_tree)) in
  let oc = open_out fname in
  output_tree (Format.formatter_of_out_channel oc) tree;
  close_out oc

(** {3 Binary constraints nodes} *)

(** A helper type to process [choose] results uniformly. *)
type bin_cstr =
  | Fv of FVcstr.cstr
  | Nl of NLcstr.cstr
  | Sp of int
  | Unavailable

(** {3 Clause matrix and pattern matching problem} *)

(** A clause matrix encodes a pattern matching problem.  The clause matrix {i
    C} can be denoted {i C = P → A} where {i P} is a {e pattern matrix} and {i
    A} is a column of {e actions}.  Each line of a pattern matrix is a pattern
    to which is attached an action.  When reducing a term, if a line filters
    the term, or equivalently the term matches the pattern, the term is
    rewritten to the action. *)
module CM = struct
  (** Reduction stack containing the position of the subterm and the number of
      abstractions traversed at this position. *)
  type occur_rs = (Occur.t * int) Stack.t

  (** Data needed to bind terms from the lhs into the rhs. *)
  type binding_data = int * term Bindlib.mvar

  (** A redefinition of the rule type.

      {b Note} that {!type:array} is used while {!module:Stack} could
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
    ; nonlin : NLcstr.t
    (** Non linearity constraints attached to this rule. *)
    ; freevars : FVcstr.t
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
    | NlConstrain of NLcstr.cstr
    (** [NlConstrain(c, s)] indicates a non-linearity constraint on column [c]
        regarding slot [s]. *)
    | FvConstrain of FVcstr.cstr
    (** Free variables constraint: the term matched must contain {e at most} a
        specified set of variables. *)

  (** [pp o m] prints matrix [m] to out channel [o]. *)
  let pp : t pp = fun oc m ->
    let pp_line oc r =
      Format.fprintf oc "@[<v>@[%a@]@,@[%a@]@,@[%a@]@]"
        (Format.pp_print_list ~pp_sep:Format.pp_print_space Print.pp)
        (Array.to_list r.c_lhs) FVcstr.pp r.freevars NLcstr.pp r.nonlin
    in
    let out fmt = Format.fprintf oc fmt in
    let pp_sep oc _ = Format.pp_print_string oc ";" in
    let (l1, l2) = List.split (Stack.to_list m.positions) in
    out "Positions @@ @[<h>%a@]"
      (Format.pp_print_list ~pp_sep Occur.pp) l1;
    out " -- Depth: @[<h>%a@]@,"
      (Format.pp_print_list ~pp_sep Format.pp_print_int) l2;
    out "{@[<v>@,%a@.@]}"
      (Format.pp_print_list pp_line) m.clauses

  (** [of_rules r] creates the initial pattern matrix from a list of rewriting
      rules. *)
  let of_rules : rule list -> t = fun rs ->
    let r2r {lhs; rhs; _} =
      { c_lhs = Array.of_list lhs ; c_rhs = rhs ; nonlin = NLcstr.empty
      ; freevars = FVcstr.empty ; env_builder = [] }
    in
    let size = (* Get length of longest rule *)
      if rs = [] then 0 else
      List.max ~cmp:Int.compare
        (List.map (fun r -> List.length r.Terms.lhs) rs) in
    let positions = Occur.args_of size Occur.empty
                    |> List.map (fun x -> (x, 0))
                    |> Stack.of_list
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
      among columns [c] according to a heuristic, along with the score. *)
  let pick_best_among : t -> int array -> int * float = fun mat columns->
    let scores = Array.map (fun ci -> score (get_col ci mat)) columns in
    let index = Array.max_index ~cmp:(Pervasives.compare) scores in
    (index, scores.(index))

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
  let choose : t -> (int * float) option = fun m ->
    let kept = discard_cons_free m.clauses in
    if kept = [||] then None else
    let sel_partial, score = pick_best_among m kept in
    let cind = kept.(sel_partial) in
    Some(cind, score)

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
      && not @@ List.exists (fun s -> NLcstr.constrained s nonlin)
        slots_uniq
    in
    let depths = Stack.to_list positions |> List.map snd
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
    NLcstr.is_empty nonlin && FVcstr.is_empty freevars
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
      let nlcstrs = List.map (fun r -> r.nonlin) m.clauses in
      let rnl = match NLcstr.choose nlcstrs with
        | Some(c, i) -> (Nl(c), i)
        | None       -> (Unavailable, 0.)
      in
      let fvcstrs = List.map (fun r -> r.freevars) m.clauses in
      let rfv = match FVcstr.choose fvcstrs with
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
    let _, (_, de), _ = Stack.destruct cm.positions ci in
    let st_r r =
      match r.c_lhs.(ci) with
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
    let _, (_, depth), _ = Stack.destruct pos ci in
    let t = r.c_lhs.(ci) in
    match fst (get_args t) with
    | Patt(i, _, e) ->
        let freevars = if (Array.length e) <> depth
          then FVcstr.instantiate slot
              (Array.map to_tvar e)
              r.freevars
          else r.freevars
        in
        let nonlin =
          match i with
          | Some(i) -> NLcstr.instantiate slot i r.nonlin
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
      let l, m, r = Stack.destruct pos ci in
      let occ, depth = m in
      let _, _, nargs = get_args_len pat in
      let replace = Occur.args_of nargs occ
                    |> List.map (fun x -> (x, depth))
      in
      Stack.restruct l replace r in
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
      let l, _, r = Stack.destruct pos ci in
      Stack.restruct l [] r
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
    let l, (occ, depth), r = Stack.destruct pos ci in
    let occ = Occur.sub occ in (* Position of term inside lambda. *)
    let pos = Stack.restruct l [(occ, depth + 1)] r in
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
  let nl_succeed : NLcstr.cstr -> clause list -> clause list = fun c ->
    List.map (fun r -> {r with nonlin = NLcstr.remove c r.nonlin})

  (** [nl_fail c r] computes the clauses not failing a non-linearity
      constraint [c] among clauses [r]. *)
  let nl_fail : NLcstr.cstr -> clause list -> clause list = fun c ->
    List.filter (fun r -> not (NLcstr.is_instantiated c r.nonlin))

  (** [fv_suceed c r] computes the clauses from [r] that verify a free
      variables constraint [c]. *)
  let fv_succeed : FVcstr.cstr -> clause list -> clause list = fun c ->
    List.map (fun r -> {r with freevars = FVcstr.remove c r.freevars})

  (** [fv_fail c r] computes the clauses not failing a free variable
      constraint [c] among clauses [r]. *)
  let fv_fail : FVcstr.cstr -> clause list -> clause list = fun c ->
    List.filter (fun r -> not (FVcstr.is_instantiated c r.freevars))
end

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
      let (i, j) = NLcstr.export constr in
      Cond({ok ; cond = Constr_Eq(i, j) ; fail})
  | FvConstrain(constr)                      ->
      let ok = compile {pats with clauses = CM.fv_succeed constr clauses} in
      let fail = compile {pats with clauses = CM.fv_fail constr clauses} in
      let (slot, vars) = FVcstr.export constr in
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
  match symb.sym_mode with
  | Const         -> () (* Constant symbols do not have rules. *)
  | Defin | Injec ->
      let tree = lazy (compile (CM.of_rules !(symb.sym_rules))) in
      let cap = lazy (Tree_types.tree_capacity (Lazy.force tree)) in
      symb.sym_tree := (cap, tree)
