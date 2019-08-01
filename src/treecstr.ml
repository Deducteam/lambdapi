(** Model of binary constraints to be used in decision trees. *)

open Extra
open Terms

(** Holds a constraint to solve and its heuristic score, or nothing if there
    are no constraint available. *)
type 'a cdecision = ('a * float) option

(** Binary constraints allow to check properties on terms during evaluation.
    A constraint is binary as it gives birth to two trees, one used if the
    constraint is satisfied and the other if not.

    Currently, binary constraints are used
    - to check non linear constraints in the left hand side of a rule (e.g. in
      presence of the rule like [f &X &X (s &Y) → r]).  In this case, the
      constraint node created will force the rewriting engine to verify that
      the terms at position [{0}] and [{1}] are convertible.
    - to verify which variables are free in a term.  If there is a rule of the
      form [f (λ x y, &Y[y]) → &Y], then the rewriting engine must verify that
      the term at position [{0.0}] depends only on free variable [y].

    Constraints depend heavily on the {!val:vars} array used to store terms
    during evaluation as it is the only way to have access to terms matched
    while evaluating.  The term {i slot} refers to a position in this
    array. *)

(** A general type for a pool of constraints.  Constraints are added on the
    fly during tree build.  Constraints can involve one or more terms from a
    lhs.  If a constraint involves more than one variable, on the first var
    encountered, the constraint is {e partially} instantiated, waiting for
    another variable to complete the constraint. *)
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
  type decision = cstr cdecision

  (** [pp_cstr o c] prints constraint [c] to channel [o]. *)
  val pp_cstr : cstr pp

  (** [pp o p] prints pool [p] to channel [o]. *)
  val pp : t pp

  (** The empty set of constraints. *)
  val empty : t

  (** [is_empty p] returns whether pool [p] is empty. *)
  val is_empty : t -> bool

  (** [instantiate i d q] instantiate constraint on slot [i] in pool [q], that
      is.  Typically, if a constraint involves only one variable, then
      instantiating a variable is equivalent to instantiating a constraint.
      However, if a constraint involves several variables, then instantiating
      a variable will promote the constraint to a {e partially instantiated
      state}, and will be completely instantiated when all the variables are
      instantiated.  The [d] is some additional data needed.
      @raise Not_found if [p] is not part of any constraint in [q]. *)
  val instantiate : int -> data -> t -> t

  (** [is_instantiated c p] returns whether pool [p] has constraint [c]
      instantiated. *)
  val is_instantiated : cstr -> t -> bool

  (** [remove c p] removes constraint [c] from pool [p]. *)
  val remove : cstr -> t -> t

  (** [score p] returns the action to take regarding pool of constraints
      [p]. *)
  val score : t -> decision

  (** [export c] returns the two slots containing the terms that must be
      convertible. *)
  val export : cstr -> out

  (** The following picks the constraint with highest priority. *)
  val choose : t list -> (cstr * float) option
end

let choose : ('a -> 'b cdecision) -> 'a list -> 'b cdecision = fun score l ->
  let cmp s1 s2 =
    match (s1, s2) with
    | (None      , None      ) -> 0
    | (None      , _         ) -> -1
    | (Some(_, x), None      ) -> max (int_of_float x) 1
    | (Some(_, x), Some(_, y)) -> compare x y
  in
  match l with
  | [] -> None
  | _  -> List.max ~cmp (List.map score l)

(** Non linearity constraints involving at least two variables. *)
module NLcstr : sig
  (** Binary constraint with
      - as {!type:data} a slot of the [vars] array,
      - as {!type:out} a couple of two slots of the [vars] array. *)
  include BinConstraintPoolSig
    with type out = int * int
     and type data = int

  (** [constrained s p] returns whether slot [s] is constrained in pool
      [p]. *)
  val constrained : data -> t -> bool
end = struct
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

  (** Weight given to nl constraints. *)
  let nl_prio = 1.

  (** A non linearity constraint. *)
  type t =
    { partial : int IntMap.t
    (** An association [(e, v)] is a slot [e] of the [env] array with a slot
        [v] of the [vars] array. *)
    ; available : IntPairSet.t
    (** Pairs of this set are checkable constraints, i.e. the two integers
        refer to available positions in the {!val:vars} array. *) }

  type cstr = int * int

  type decision = cstr cdecision

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

  let empty = { partial = IntMap.empty ; available = IntPairSet.empty }

  let is_empty { available ; _ } = IntPairSet.is_empty available

  let normalize (i, j) = if Int.compare i j < 0 then (i, j) else (j, i)

  let constrained : data -> t -> bool = fun slot pool ->
    IntMap.mem slot pool.partial

  let score c =
    if is_empty c then None else
    Option.bind (fun c -> Some(c, nl_prio))
      (try Some(IntPairSet.choose c.available)
       with Not_found -> None)

  let is_instantiated pair { available ; _ } = IntPairSet.mem pair available

  let remove pair pool = { pool with
                           available = IntPairSet.remove pair pool.available }

  let export pair = pair

  let instantiate vslot esl pool =
    try
      let ovs = IntMap.find esl pool.partial in
      let available = IntPairSet.add (normalize (vslot, ovs))
          pool.available in
      { pool with available }
    with Not_found -> { pool with
                        partial = IntMap.add esl vslot pool.partial }

  (** [choose s] returns the constraint having the highest score in [s]. *)
  let choose = choose score
end

(** Free variables constraints.  Such a constraint involves only one variable,
    but it requires the list of variables that may appear free in the term. *)
module FVcstr : sig
  (** Binary constraint with
      - as {!type:data} an array of free variables,
      - as {!type:out} the slot of the [vars] array and an array of variables
        that may appear free in the term. *)
  include BinConstraintPoolSig
    with type out = int * tvar array
     and type data = tvar array
end = struct
  type t = (tvar array) IntMap.t

  type cstr = int * tvar array

  type decision = cstr cdecision

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

  let is_instantiated (sl, x) p =
    try Array.equal Bindlib.eq_vars x (IntMap.find sl p)
    with Not_found -> false

  let remove (sl, x) p =
    try
      if Array.equal Bindlib.eq_vars x (IntMap.find sl p) then
        IntMap.remove sl p
      else p
    with Not_found -> p

  let instantiate = IntMap.add

  let export x = x

  let score c = try Some(IntMap.choose c, 1.0) with Not_found -> None

  (** [choose s] returns the constraint having the highest score in [s]. *)
  let choose = choose score
end
