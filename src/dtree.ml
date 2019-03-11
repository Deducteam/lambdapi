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

(* Redefinition for function [mark] as it uses a not generalizable type, it
   couldn't be put into extra (and we need Position in {!module:Terms} as
   well). *)
module Position =
struct
  include Position

  (** [mark l] enriches elements of [l] attaching a position to them. *)
  let mark : 'a list -> ('a * t) list = List.mapi (fun i e -> (e, [i]))
end

(** [iter l n f t] is a generic iterator on trees; with function [l] performed
    on leaves, function [n] performed on nodes, [f] returned in case of
    {!const:Fail} on tree [t]. *)
let iter : (int IntMap.t -> int PosMap.t -> action -> 'a) ->
  (int option -> bool -> (term option * 'a) list -> 'a) ->
  'a -> t -> 'a = fun do_leaf do_node fail t ->
  let rec loop = function
    | Leaf(pa, re, a)                                -> do_leaf pa re a
    | Fail                                           -> fail
    | Node({ swap = p ; push = pu ; children = ch }) ->
      do_node p pu (List.map (fun (teo, c) -> (teo, loop c)) ch) in
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
  let rec write_tree : int -> term option -> t -> unit =
    fun father_l swon tree ->
    match tree with
    | Leaf(_, _, a) ->
      incr nodecount ;
      F.fprintf ppf "@ %d [label=\"" !nodecount ;
      let _, acte = Bindlib.unmbind a in
      P.pp ppf acte ; F.fprintf ppf "\"]" ;
      F.fprintf ppf "@ %d -- %d [label=\"" father_l !nodecount ;
      pp_opterm ppf swon ; F.fprintf ppf "\"];"
    | Node(ndata)   ->
      let { swap ; children ; push } = ndata in
      incr nodecount ;
      let tag = !nodecount in
      begin (* Create node *)
        F.fprintf ppf "@ %d [label=\"" tag ;
        F.fprintf ppf "%d" (match swap with None -> 0 | Some(i) -> i) ;
        F.fprintf ppf "\"" ;
        if push then F.fprintf ppf " shape=\"box\"" ;
        F.fprintf ppf "]"
      end ;
      begin (* Create edge *)
        F.fprintf ppf "@ %d -- %d [label=\"" father_l tag ;
        pp_opterm ppf swon ; F.fprintf ppf "\"];"
      end ;
      List.iter (fun (s, e) -> write_tree tag s e) children ;
    | Fail          ->
      incr nodecount ;
      F.fprintf ppf "@ %d -- %d [label=\"%s\"];" father_l !nodecount "f"
  in
  begin
    match tree with
    (* First step must be done to avoid drawing a top node. *)
    | Node({ swap ; children = ch ; push }) ->
       F.fprintf ppf "@ 0 [label=\"%d\""
         (match swap with None -> 0 | Some(i) -> i) ;
       if push then F.fprintf ppf " shape=\"box\"" ;
       F.fprintf ppf "]" ;
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
  type line = (term * Position.t) list

  (** A redefinition of the rule type. *)
  type rule = { lhs : line
              (** Left hand side of a rule. *)
              ; rhs : action ref
              (** Right hand side of a rule. *) }

  (** The core data, contains the rewrite rules. *)
  type matrix = rule list

  (** Type of a matrix of patterns.  Each line is a row having an attached
      action. *)
  type t = { values : matrix
           (** The rules. *)
           ; var_catalogue : Position.t list
           (** Contains positions of terms in {!recfield:lhs} that can be used
               as variables in {!recfield:rhs}. *)}

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

  (** [of_rules r] creates the initial pattern matrix from a list of rewriting
      rules. *)
  let of_rules : Terms.rule list -> t = fun rs ->
    { values = List.map (fun r ->
      let term_pos = Position.mark r.Terms.lhs in
      { lhs = term_pos ; rhs = ref r.Terms.rhs }) rs
    ; var_catalogue = [] }

  (** [is_empty m] returns whether matrix [m] is empty. *)
  let is_empty : t -> bool = fun m -> m.values = []

  (** [get_col n m] retrieves column [n] of matrix [m].  There is some
      processing because all rows do not have the same length. *)
  let get_col : int -> t -> line = fun ind { values ; _ } ->
    let opcol = List.fold_left (fun acc { lhs = li ; _ } ->
        List.nth_opt li ind :: acc) []
        values in
    let rem = List.filter (function None -> false | Some(_) -> true) opcol in
    List.map (function Some(e) -> e | None -> assert false) rem

  (** [select m i] keeps the columns of [m] whose index are in [i]. *)
  let select : t -> int array -> t = fun m indexes ->
    { m with
      values = List.map (fun rul ->
        { rul with
          lhs = Array.fold_left (fun acc i -> List.nth rul.lhs i :: acc)
            [] indexes }) m.values }

  (** [swap p i] swaps the first column with the [i]th one. *)
  let swap : t -> int -> t = fun pm c ->
    { pm with values = List.map (fun rul ->
      { rul with lhs = List.swap_head rul.lhs c }) pm.values }
      (* XXX change with [List.bring]. *)

  (** [cmp c d] compares columns [c] and [d] returning: +1 if [c > d], 0 if
      [c = d] or -1 if [c < d]; where [<], [=] and [>] are defined according
      to a heuristic.  *)
  let cmp : line -> line -> int = fun _ _ -> 0

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
    let ncols = List.fold_left (fun acc { lhs ; _ } ->
        let le = List.length lhs in
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

  (** [update_catalogue c r] updates catalogue of vars [c] with rule [r]. *)
  let update_catalogue : Position.t list -> rule -> Position.t list =
    fun varstack rule ->
      let { lhs ; _ } = rule in
      match List.hd lhs with
      | Patt(Some(_), _, _), p -> p :: varstack
      | _                      -> varstack

  (** [pos_needed_by l] returns a mapping from position of variables into [l]
      to the slot assigned to each variable in a {!type:term_env}. *)
  let pos_needed_by : line -> int PosMap.t = fun  lhs ->
    let module Po = Position in
    let rec loop : term list -> Po.t -> int PosMap.t = fun st po ->
      match st with
      | [] -> PosMap.empty
      | x :: xs ->
         begin
           match x with
           | Patt(None, _, _)
           | Symb(_, _)          -> loop xs (Po.succ po)
           | Patt(Some(i), _, _) -> PosMap.add po i (loop xs (Po.succ po))
           | Appl(_, _)          ->
              let _, args = Basics.get_args x in
              let xpos = loop args Po.init in
              let nxpos = PosMap.fold (fun xpo slot nmap ->
                PosMap.add (Po.prefix po xpo) slot nmap) PosMap.empty xpos in
              PosMap.union (fun _ _ -> assert false) nxpos
                (loop xs (Po.succ po))
           | _                   -> assert false
         end in
    loop (List.map fst lhs) Po.init
end

module Pm = Pattmat

(** [spec_filter p l] returns whether a line [l] (of a pattern matrix) must be
    kept when specializing the matrix on pattern [p]. *)
let rec spec_filter : term -> term list -> bool = fun pat li ->
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
  | Symb(s, _)  , Symb(s', _)             -> s == s'
  | Appl(u1, u2), Appl(v1, v2)            ->
    spec_filter u1 (v1 :: litl) && spec_filter u2 (v2 :: litl)
  (* ^ Verify there are as many Appl (same arity of leftmost terms).  Check of
       left arg of Appl is performed in [matching], so we perform it here. *)
  | Abst(_, b1)         , Abst(_, b2)     ->
    let _, u, v = Bindlib.unbind2 b1 b2 in
    spec_filter u (v :: litl)
  | Vari(x)     , Vari(y)                 -> Bindlib.eq_vars x y
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
  | Symb(_, _), _ -> litl
  | Appl(u, v), p ->
  (* ^ Nested structure verified in filter *)
    let upat = fst @@ Basics.get_args pat in
    let np = Position.prefix p Position.init in
    spec_line upat ((u, np) :: (v, Position.succ np) :: litl)
  | Abst(_, b), p ->
     let np = Position.prefix p Position.init in
     let _, t = Bindlib.unbind b in (t, np) :: litl
  | Vari(_), _    -> litl
  | _ -> (* Cases that require the pattern *)
    match lihd, pat with
    | (Patt(_, _, [| |]), p), Appl(_, _) ->
    (* ^ Wildcard *)
      let arity = List.length @@ snd @@ Basics.get_args pat in
      List.init arity (fun i ->
        Patt(None, "w", [| |]), Position.prefix p [i]) @ litl
    | (Patt(_, _, _), p)    , Abst(_, b) ->
       let _, t = Bindlib.unbind b in
       (t, Position.prefix p Position.init) :: litl
    | (Patt(_, _, _), _)    , _          -> litl
    | (x, _)                , y          ->
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
  let filtered = List.filter (fun { Pm.lhs = l ; _ } ->
      spec_filter p (List.map fst l)) m.values in
  let newmat = List.map (fun rul ->
      { rul with Pm.lhs = spec_line p rul.Pm.lhs }) filtered in
  let newstack = List.fold_left Pm.update_catalogue m.var_catalogue
    m.values in
  { values = newmat ; var_catalogue = newstack }

(** [default m] computes the default matrix containing what remains to be
    matched if no specialization occurred. *)
let default : Pm.t -> Pm.t = fun { values = m ; var_catalogue = vs } ->
  let filtered = List.filter (fun { Pm.lhs = l ; _ } ->
      match fst @@ List.hd l with
      | Patt(_ , _, _)                       -> true
      | Symb(_, _) | Abst(_, _) | Appl(_, _) -> false
      | Vari(_)                              -> false
      | x                                    ->
        Print.pp Format.err_formatter x ;
        assert false) m in
  let unfolded = List.map (fun rul ->
      match List.hd rul.Pm.lhs with
      | Patt(_, _, _), _ ->
        { rul with Pm.lhs = List.tl rul.Pm.lhs }
      | _             -> assert false) filtered in
  let newst = List.fold_left Pm.update_catalogue vs m in
  { values = unfolded ; var_catalogue = newst }

(** [is_cons t] returns whether [t] can be considered as a constructor. *)
let rec is_cons : term -> bool = function
  | Symb(_, _) | Abst(_, _) -> true
  | Appl(u, _)              -> is_cons u
  | _                       -> false

(** [compile m] returns the decision tree allowing to parse efficiently the
    pattern matching problem contained in pattern matrix [m]. *)
let compile : Pm.t -> t = fun patterns ->
  let rule2needed_pos = List.map (fun rule -> (* Retrieve vars positions *)
    (rule.Pm.rhs, Pm.pos_needed_by rule.lhs)) patterns.Pm.values in
  let rec grow : Pm.t -> t = fun pm ->
    let { Pm.values = m ; Pm.var_catalogue = vcat } = pm in
    (* Pm.pp Format.std_formatter pm ; *)
    if Pm.is_empty pm then
      begin
        failwith "matching failure" ; (* For debugging purposes *)
        (* Dtree.Fail *)
      end
    else
      if Pm.exhausted (List.hd m) then
        (* If there are no pattern that can be matched remaining, retrieve all
           pattern variables *)
        let rhs = (List.hd m).Pm.rhs in
        let pos2slot = List.assq rhs rule2needed_pos in
        (* [env_builder] maps future position in the term stack to the slot in
           the environment. *)
        let env_builder = snd @@ List.fold_left (fun (i, m) tpos ->
          let opslot = PosMap.find_opt tpos pos2slot in
          match opslot with
          | None     -> succ i, m
          (* ^ The stack may contain more variables than needed for the
             rule *)
          | Some(sl) -> succ i, IntMap.add i sl m) (0, IntMap.empty) vcat in
        let remain_loc =
          if (IntMap.cardinal env_builder = PosMap.cardinal pos2slot)
          then PosMap.empty else
            let remains = Position.mark (List.map (fst) (List.hd m).lhs) in
            Pm.pos_needed_by remains in
          Leaf(env_builder, remain_loc, !((List.hd m).Pm.rhs))
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
        let push = (* Push if there is a pattern variable in fcol *)
          let rec loop : term list -> bool = function
            | []                       -> false
            | Patt(Some(_), _, _) :: _ -> true
            | _ :: xs                  -> loop xs in
          loop (List.map fst fcol) in
        let cons = List.filter is_cons (List.map fst fcol) in
        let spepatts = List.map (fun s ->
          (Some(fst @@ Basics.get_args s), specialize s spm)) cons in
        let defpatts = (None, default spm) in
        let children =
          List.map (fun (c, p) -> (c, grow p))
            (spepatts @ (if Pm.is_empty (snd defpatts)
                         then [] else [defpatts])) in
        Node({ swap = swap ; children = children
             ; push = push }) in
  grow patterns
