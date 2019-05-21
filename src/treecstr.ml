(** This module provides a model of binary constraints to be used in decision
    trees. *)
open Terms
open Basics
open Extra

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
      the term at position [{0}] depends only on free variables [x] and [y]
      and that the term at position [{1}] depends only on free variable [y].

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

  (** Type used for export, to be used during evaluation. *)
  type out

  (** Auxiliary data used to instantiate a constraint. *)
  type data

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

  (** [instantiate p i d q] instantiates path [p] in pool [q] using index [i],
      that is, mark a path as {i seen} in the constraints.  Typically, if a
      constraint involves only one variable, then instantiating a variable is
      equivalent to instantiating a constraint.  However, if a constraint
      involves several variables, then instantiating a variable will promote
      the constraint to a {e partially instantiated state}, and will be
      completely instantiated when all the variables are instantiated.  The
      [d] is some additional data needed.
      @raise Not_found if [p] is not part of any constraint in [q]. *)
  val instantiate : Subterm.t -> int -> data -> t -> t

  (** [is_instantiated c p] returns whether pool [p] has constraint [c]
      instantiated. *)
  val is_instantiated : cstr -> t -> bool

  (** [remove c p] removes constraint [c] from pool [p]. *)
  val remove : cstr -> t -> t

  (** [score p] returns the action to take regarding pool of constraints
      [p]. *)
  val score : t -> decision

  (** [of_terms r] returns constraint pool induced by terms in [r]. *)
  val of_terms : term list -> t

  (** [export c] returns the two slots containing the terms that must be
      convertible. *)
  val export : cstr -> out
end

(** Non linearity constraints signature.  A non linearity constraint involves
    at least two variables. *)
module type NlConstraintSig =
sig
  include BinConstraintPoolSig with type out = int * int
                                and type data = int
end

(** Free variables constraints.  Such a constraint involves only one variable,
    but it requires the list of variables that may appear free in the term. *)
module type FvConstraintSig =
sig
  include BinConstraintPoolSig with type out = int * tvar array
                                and type data = tvar array
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
    { partial : int IntMap.t
    (** An association [(e, v)] is a slot [e] of the [env] array with a slot
        [v] of the [vars] array. *)
    ; available : IntPairSet.t
    (** Pairs of this set are checkable constraints, i.e. the two integers
        refer to available positions in the {!val:vars} array. *) }

  type cstr = int * int

  type decision = Solve of cstr * int
                | Instantiate of Subterm.t * int
                | Unavailable

  type out = int * int

  type data = int

  let pp_cstr oc (i, j) = Format.fprintf oc "(%d,%d)" i j

  let pp oc pool =
    let module F = Format in
    let pp_int_int oc (i, j) = F.fprintf oc "@[(%d, %d)@]" i j in
    let pp_partial oc ism =
      F.fprintf oc "@[partial: %a@]"
        (F.pp_print_list
           ~pp_sep:(fun oc () -> F.pp_print_string oc ";")
           pp_int_int)
        (IntMap.bindings ism) in
    let pp_available oc ips =
      F.fprintf oc "@[available: %a@]"
        (F.pp_print_list
           ~pp_sep:(fun oc () -> F.pp_print_string oc ";")
           pp_int_int)
        (IntPairSet.elements ips) in
    F.fprintf oc "Nl constraints:@," ;
    F.fprintf oc "@[<v>" ;
    F.fprintf oc "%a@," pp_partial pool.partial ;
    F.fprintf oc "%a@," pp_available pool.available ;
    F.fprintf oc "@]"

  let empty = { partial = IntMap.empty
              ; available = IntPairSet.empty }

  let is_empty { available ; _ } =
    IntPairSet.is_empty available

  let normalize (i, j) = if Int.compare i j < 0 then (i, j) else (j, i)

  let score c =
    if is_empty c then Unavailable else
    match IntPairSet.choose_opt c.available with
    | Some(c) -> Solve(c, 1)
    | None    -> Unavailable

  let is_instantiated pair { available ; _ } = IntPairSet.mem pair available

  let concerns _ _ = assert false

  let remove pair pool = { pool with
                           available = IntPairSet.remove pair pool.available }

  let export pair = pair

  let instantiate _ vslot esl pool =
    match IntMap.find_opt esl pool.partial with
    | Some(ovs) ->
        let available = IntPairSet.add (normalize (vslot, ovs))
            pool.available in
        { pool with available }
    | None     ->
        let partial = IntMap.add esl vslot pool.partial in
        { pool with partial }

  (** [of_terms r] returns the non linearity set of constraints associated to
      list of terms [r]. *)
  let of_terms _ = assert false
end

module FvConstraints : FvConstraintSig =
struct
  type t = (tvar array) IntMap.t

  type cstr = int * tvar array

  type decision = Solve of cstr * int
                | Instantiate of Subterm.t * int
                | Unavailable

  type out = int * tvar array

  type data = tvar array

  let pp_cstr oc (sl, vars) =
    let module F = Format in
    Format.fprintf oc "%d: {@[<h>%a@]}" sl
      (Format.pp_print_list
         ~pp_sep:(fun oc () -> Format.pp_print_string oc "; ") Print.pp_tvar)
      (Array.to_list vars)

  let pp oc available =
    let module F = Format in
    let pp_tvs : tvar list pp = F.pp_print_list
        ~pp_sep:(fun oc () -> F.fprintf oc "; ")
        Print.pp_tvar in
    let ppit : (int * tvar array) pp = fun oc (a, b) ->
      F.fprintf oc "@[(%d, %a)@]" a pp_tvs (Array.to_list b) in
    F.fprintf oc "Fv constraints:@," ;
    F.fprintf oc "@[<v>" ;
    F.fprintf oc "@[available: %a@]@,"
      (F.pp_print_list ppit)
      (IntMap.bindings available) ;
    F.fprintf oc "@]@."

  let empty = IntMap.empty

  let is_empty = IntMap.is_empty

  let concerns _ _ = assert false

  let is_instantiated (sl, x) p =
    match IntMap.find_opt sl p with
    | None     -> false
    | Some(x') -> Array.equal Bindlib.eq_vars x x'

  let remove (sl, x) p =
    match IntMap.find_opt sl p with
    | None     -> p
    | Some(x') ->
        if Array.equal Bindlib.eq_vars x x'
        then IntMap.remove sl p
        else p

  let instantiate _ slot vars pool =
    IntMap.add slot vars pool

  let export x = x

  let of_terms _ = assert false

  let score c =
    if is_empty c then Unavailable else
    match IntMap.choose_opt c with
    | Some(i, x) -> Solve((i, x), 1)
    | None       -> Unavailable
end

(** {3 Comparing constraints }*)

(** Type making a module comparable. *)
module type Scorable = sig
  (** Type of the element to score. *)
  type t

  (** Result of a comparison. *)
  type decision

  (** [choose x] returns the action with the highest score. *)
  val choose : t list -> decision
end

(** [MakeScorable(P)] returns a module containing a function to compare list
    of elements of [P].  Acts as an {e extension} of [P]. *)
module MakeScorable(BCP:BinConstraintPoolSig)
  : (Scorable with type t := BCP.t and type decision := BCP.decision) =
struct

  open BCP

  let score_lt s1 s2 = match (s1, s2) with
    | Unavailable, Unavailable -> true
    | Unavailable, _           -> true
    | _          , Unavailable -> false
    | Solve(_, s), Solve(_, t) -> s <= t
    | Solve(_, _), _           -> false
    | _          , Solve(_, _) -> true
    | Instantiate(_, s), Instantiate(_, t) -> s <= t

  let choose = function
    | [] -> Unavailable
    | cs -> List.map score cs |> List.extremum score_lt
end

(** Non linearity with score constraints. *)
module type NlScorableSig = sig
  type t
  type cstr
  type decision = Solve of cstr * int
                | Instantiate of Subterm.t * int
                | Unavailable
  include (NlConstraintSig)
          with type t := t and type cstr := cstr and type decision := decision

  include Scorable
      with type t := t and type decision := decision
end

(** Free variables constraints with score. *)
module type FvScorableSig = sig
  type t
  type cstr
  type decision = Solve of cstr * int
                | Instantiate of Subterm.t * int
                | Unavailable
  include (FvConstraintSig)
          with type t := t and type cstr := cstr and type decision := decision

  include Scorable
      with type t := t and type decision := decision
end

module NlScorable : NlScorableSig = struct
  include NlConstraints
  include MakeScorable(NlConstraints)
end

module FvScorable : FvScorableSig = struct
  include FvConstraints
  include MakeScorable(FvConstraints)
end
