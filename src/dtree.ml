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

(** {b Example} Given a rewrite system for a symbol [plus] given as (in
    [plus.dk])
    - [plus Z (S m)     → S m]
    - [plus n Z         → n]
    - [plus (S n) (S m) → S (S m)]

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
let iter : (action -> 'a) -> (int option -> (term option * 'a) list -> 'a) ->
  'a -> t -> 'a = fun do_leaf do_node fail t ->
  let rec loop = function
    | Leaf(a)                            -> do_leaf a
    | Fail                               -> fail
    | Node({ swap = p ; children = ch }) ->
      do_node p (List.map (fun (teo, c) -> (teo, loop c)) ch) in
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
    | None    -> F.fprintf oc "d" in
  let rec write_tree : int -> term option -> t -> unit =
    fun father_l swon tree ->
  (* We cannot use iter since we need the father to be passed. *)
    match tree with
    | Leaf(a)  ->
      incr nodecount ;
      F.fprintf ppf "@ %d [label=\"" !nodecount ;
      let _, acte = Bindlib.unmbind a in
      P.pp ppf acte ; F.fprintf ppf "\"]" ;
      F.fprintf ppf "@ %d -- %d [label=\"" father_l !nodecount ;
      pp_opterm ppf swon ; F.fprintf ppf "\"];"
    | Node(ndata) ->
      let { swap = swa ; children = ch ; _ } = ndata in
      incr nodecount ;
      let tag = !nodecount in
      F.fprintf ppf "@ %d [label=\"" tag ;
      F.fprintf ppf "%d" (match swa with None -> 0 | Some(i) -> i) ;
      F.fprintf ppf "\"]" ;
      F.fprintf ppf "@ %d -- %d [label=\"" father_l tag ;
      pp_opterm ppf swon ; F.fprintf ppf "\"];" ;
      List.iter (fun (s, e) -> write_tree tag s e) ch ;
    | Fail        ->
      incr nodecount ;
      F.fprintf ppf "@ %d -- %d [label=\"%s\"];" father_l !nodecount "f"
  in
  begin
    match tree with
    (* First step must be done to avoid drawing a top node. *)
    | Node({ swap = _ ; children = ch ; _ }) ->
      List.iter (fun (sw, c) -> write_tree 0 sw c) ch
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
  type line = term list

  (** A redefinition of the rule type. *)
  type rule = { lhs : line
              (** Left hand side of a rule. *)
              ; rhs : action
              (** Right hand side of a rule. *) }

  (** The core data, contains the rewrite rules. *)
  type matrix = rule list

  (** Type of a matrix of patterns.  Each line is a row having an attached
      action.
      XXX keep record? *)
  type t = { values : matrix }

  (** [pp_line o l] prints line [l] to out channel [o]. *)
  let pp_line : line pp = List.pp Print.pp ";"

  (** [pp o m] prints matrix [m] to out channel [o]. *)
  let pp : t pp = fun oc { values = va ; _ } ->
    let module F = Format in
    F.fprintf oc "[|@[<v>@," ;
    List.pp pp_line "\n  " oc (List.map (fun { lhs = l ; _ } -> l) va) ;
    (* List.pp does not process Format "@" directives when in sep *)
    F.fprintf oc "@.|]@,@?"

  (** [of_rules r] creates the initial pattern matrix from a list of rewriting
      rules. *)
  let of_rules : Terms.rule list -> t = fun rs ->
    { values = List.map (fun r ->
          { lhs = r.Terms.lhs ; rhs = r.Terms.rhs }) rs }

  (** [is_empty m] returns whether matrix [m] is empty. *)
  let is_empty : t -> bool = fun m -> m.values = []

  (** [get_col n m] retrieves column [n] of matrix [m].  There is some
      processing because all rows do not have the same length. *)
  let get_col : int -> t -> line = fun ind { values = valu ; _ } ->
    let opcol = List.fold_left (fun acc { lhs = li ; _ } ->
        List.nth_opt li ind :: acc) []
        valu in
    let rem = List.filter (function None -> false | Some(_) -> true) opcol in
    List.map (function Some(e) -> e | None -> assert false) rem

  (** [select m i] keeps the columns of [m] whose index are in [i]. *)
  let select : t -> int array -> t = fun m indexes ->
    { values = List.map (fun rul ->
          { rul with
            lhs = Array.fold_left (fun acc i -> List.nth rul.lhs i :: acc)
                [] indexes }) m.values }

  (** [swap p i] swaps the first column with the [i]th one. *)
  let swap : t -> int -> t = fun pm c ->
    { values = List.map (fun rul ->
      { rul with lhs = List.swap_head rul.lhs c }) pm.values }

  (** [cmp c d] compares columns [c] and [d] returning: +1 if [c > d], 0 if
      [c = d] or -1 if [c < d]; where [<], [=] and [>] are defined according
      to a heuristic.  *)
  let cmp : line -> line -> int = fun _ _ -> 0

  (** [pick_best m] returns the index of the best column of matrix [m]
      according to a heuristic. *)
  let pick_best : t -> int = fun _ -> 0

  (** [is_pattern t] returns whether a term [t] is considered as a pattern *)
  let rec is_pattern : term -> bool = function
    | Patt(_, _, _) -> false
    | _             -> true

  (** [exhausted r] returns whether rule [r] can be further pattern matched or
      if it is ready to yield the action.  A rule is exhausted when its left
      hand side is composed only of wildcards. *)
  let exhausted : rule -> bool = fun { lhs ; _ }->
    let rec loop = function
      | []                       -> true
      | x :: _ when is_pattern x -> false
      | _ :: xs                  -> loop xs in
    loop lhs

  (** [can_switch_on p k] returns whether a switch can be carried out on
      column [k] in matrix [p] *)
  let can_switch_on : t -> int -> bool = fun { values = valu ; _ } k ->
    let rec loop : rule list -> bool = function
      | []      -> true
      | r :: rs ->
        begin
          match List.nth_opt r.lhs k with
          | None    -> loop rs
          | Some(t) -> is_pattern t
        end in
    loop valu

  (** [discard_patt_free m] returns the list of indexes of columns containing
      terms that can be matched against (discard pattern-free columns). *)
  let discard_patt_free : t -> int array = fun m ->
    let ncols = List.fold_left (fun acc { lhs = l ; _ } ->
        let le = List.length l in
      if le > acc then le else acc) 0 m.values in
    let switchable = List.init ncols (fun k ->
        can_switch_on m k) in
    let indexes = List.mapi (fun k cm ->
        if cm then Some(k) else None) switchable in
    let remaining = List.filter (function
        | None    -> false
        | Some(_) -> true) indexes in
    let unpacked = List.map (function
        | Some(k) -> k
        | None    -> assert false) remaining in
    assert ((List.length unpacked) > 0) ;
    Array.of_list unpacked
end

module Pm = Pattmat

(** [spec_filter p l] returns whether a line [l] (of a pattern matrix) must be
    kept when specializing the matrix on pattern [p]. *)
let rec spec_filter : term -> Pm.line -> bool = fun pat li ->
  (* Might be relevant to reduce the function to [term -> term -> bool] with
     [spec_filter p t] testing pattern [p] against head of line [t] *)
  let lihd, litl = match li with
    | x :: xs -> x, xs
    | []      -> assert false in
  match pat, lihd with
  | _           , Patt(None, _, [| |])    -> true
  (* ^ Wildcard or linear var not appearing in rhs *)
  | _           , Patt(Some(_), _, [| |]) -> true
  (* ^ Linear var appearing in rhs *)
  | Symb(s, _)  , Symb(s', _)            -> s == s'
  | Appl(u1, u2), Appl(v1, v2)           ->
    spec_filter u1 (v1 :: litl) && spec_filter u2 (v2 :: litl)
  (* ^ Verify there are as many Appl (same arity of leftmost terms).  Check of
       left arg of Appl is performed in [matching], so we perform it here. *)
  | Abst(_, b1)         , Abst(_, b2)    ->
    let _, u, v = Bindlib.unbind2 b1 b2 in
    spec_filter u (v :: litl)
  | Vari(x)             , Vari(y)        -> Bindlib.eq_vars x y
  (* All below ought to be put in catch-all case*)
  | Symb(_, _)   , Appl(_, _)    -> false
  | Patt(_, _, _), Symb(_, _)    -> false
  | Patt(_, _, _), Appl(_, _)    -> false
  | Appl(_, _)   , Symb(_, _)    -> false
  | Appl(_, _)   , Abst(_, _)    -> false
  | Abst(_, _)   , Appl(_, _)    -> false
  | x            , y             ->
    Buffer.clear Format.stdbuf ; Print.pp Format.str_formatter x ;
    Format.fprintf Format.str_formatter "|" ;
    Print.pp Format.str_formatter y ;
    let msg = Printf.sprintf "%s: suspicious specialization-filtering"
        (Buffer.contents Format.stdbuf) in
    failwith msg

(** [spec_line p l] specializes the line [l] against pattern [p]. *)
let rec spec_line : term -> Pm.line -> Pm.line = fun pat li ->
  let lihd, litl = List.hd li, List.tl li in
  match lihd with
  | Symb(_, _)    -> litl
  | Appl(u, v)    ->
  (* ^ Nested structure verified in filter *)
    let upat = fst @@ Basics.get_args pat in
    spec_line upat (u :: v :: litl)
  | Abst(_, b)    ->
      let _, t = Bindlib.unbind b in t :: litl
  | Vari(_)       -> litl
  | _ -> (* Cases that require the pattern *)
    match lihd, pat with
    | Patt(_, _, [| |]), Appl(_, _)    ->
    (* ^ Wildcard *)
      let arity = List.length @@ snd @@ Basics.get_args pat in
      List.init arity (fun _ -> Patt(None, "w", [| |])) @ litl
    | Patt(_, _, _)       , Abst(_, b) ->
      let _, t = Bindlib.unbind b in t :: litl
    | Patt(_, _, _)       , _          -> litl
    | x                   , y          ->
      Buffer.clear Format.stdbuf ; Print.pp Format.str_formatter x ;
      Format.fprintf Format.str_formatter "|" ;
      Print.pp Format.str_formatter y ;
      let msg = Printf.sprintf "%s: suspicious specialization unfold"
          (Buffer.contents Format.stdbuf) in
      failwith msg

(** [specialize p m] specializes the matrix [m] when matching against pattern
    [p].  A matrix can be specialized by a user defined symbol, an abstraction
    or a pattern variable.  The specialization always happen on the first
    column (which is swapped if needed).  We allow specialization by
    {!cons:Appl} as it allows to check the number of successive applications.
    In case an {!cons:Appl} is given as pattern [p], only terms having the
    same number of applications and having the same leftmost {e non}
    {!cons:Appl} are considered as constructors. *)
let specialize : term -> Pm.t -> Pm.t = fun p m ->
  let up = p in
  let filtered = List.filter (fun { Pm.lhs = l ; _ } ->
      spec_filter up l) m.values in
  let newmat = List.map (fun rul ->
      { rul with Pm.lhs = spec_line up rul.Pm.lhs }) filtered in
  { values = newmat }

(** [default m] computes the default matrix containing what remains to be
    matched if no specialization occurred. *)
let default : Pm.t -> Pm.t =
  fun { values = m } ->
  let filtered = List.filter (fun { Pm.lhs = l ; _ } ->
      match List.hd l with
      | Patt(_ , _, _)                       -> true
      | Symb(_, _) | Abst(_, _) | Appl(_, _) -> false
      | Vari(_)                              -> false
      | x                                    ->
        Print.pp Format.err_formatter x ;
        assert false) m in
  let unfolded = List.map (fun rul ->
      match List.hd rul.Pm.lhs with
      | Patt(_, _, _) ->
        { rul with Pm.lhs = List.tl rul.Pm.lhs }
      | _             -> assert false) filtered in
  { values = unfolded }

(** [is_cons t] returns whether [t] can be considered as a constructor. *)
let rec is_cons : term -> bool = function
  | Symb(_, _) | Abst(_, _) -> true
  | Appl(u, _)              -> is_cons u
  | _                       -> false

(** [compile m] returns the decision tree allowing to parse efficiently the
    pattern matching problem contained in pattern matrix [m]. *)
let compile : Pm.t -> t = fun patterns ->
  let rec grow : Pm.t -> t = fun pm ->
    let { Pm.values = m } = pm in
    (* Pm.pp Format.std_formatter pm ; *)
    if Pm.is_empty pm then
      begin
        failwith "matching failure" ; (* For debugging purposes *)
        (* Dtree.Fail *)
      end
    else
      (* Look at the first line, if it contains only wildcards, then
         execute the associated action. *)
      if Pm.exhausted (List.hd m) then
        Leaf((List.hd m).Pm.rhs)
      else
        (* Pick a column in the matrix and pattern match on the constructors
           in it to grow the tree. *)
        let kept_cols = Pm.discard_patt_free pm in
        let sel_in_partial = Pm.pick_best (Pm.select pm kept_cols) in
        let swap = if kept_cols.(sel_in_partial) = 0 then None
          else Some kept_cols.(sel_in_partial) in
        let spm = match swap with
          | None    -> pm
          | Some(i) -> Pm.swap pm i in
        let fcol = Pm.get_col 0 spm in
        let cons = List.filter is_cons fcol in
        let spepatts = List.map (fun s ->
          (Some(fst @@ Basics.get_args s), specialize s spm)) cons in
        let defpatts = (None, default spm) in
        let children =
          List.map (fun (c, p) -> (c, grow p))
            (spepatts @ (if Pm.is_empty (snd defpatts)
                         then [] else [defpatts])) in
        Node({ swap = swap ; children = children }) in
  grow patterns
