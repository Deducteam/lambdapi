(** Conditions used for decision trees and heuristics.

    The decision trees used for pattern matching include binary nodes carrying
    conditions (see constructor {!constructor:Tree_types.Cond}). We test these
    conditions during evaluation to choose which branch to follow. We have two
    forms of conditions in the current implementation.
    - convertibility conditions (see module {!module:NLCond} below),
    - free variable conditions (see module {!module:FVCond} below). *)

open Extra
open Terms

(** Signature for a pool of conditions. Conditions are added on the fly during
    the construction of decision trees. Constraints can involve one or several
    patterns from a rewriting rule LHS (see {!val:instantiate}). *)
module type Cond_sig = sig
  (** Pool of constraints. *)
  type t

  (** Representation of an (instantiated) condition. *)
  type cond

  (** Auxiliary data used to instantiate a condition. *)
  type data

  (** Synonym of {!type:cond}, made concrete in the interface. *)
  type exported

  (** [pp oc pool] prints the pool [pool] to channel [oc]. *)
  val pp : t pp

  (** [pp_cond oc cond] prints condition [cond] to channel [oc]. *)
  val pp_cond : cond pp

  (** Empty set of conditions. *)
  val empty : t

  (** [is_empty pool] tells whether the pool [pool] is empty. *)
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

  (** [is_instantiated cond pool] tells whether the condition [cond] has  been
      instantiated in the pool [pool] *)
  val is_instantiated : cond -> t -> bool

  (** [remove cond pool] removes condition [cond] from the pool [pool]. *)
  val remove : cond -> t -> t

  (** [export cond] returns the exported counterpart of [cond]. *)
  val export : cond -> exported

  (** [choose pools] selects a condition to verify among [pools]. *)
  val choose : t list -> cond option
end

(** Module providing convertibility conditions, used to handle rewriting rules
    that are not left-linear, for example [f &x &x (s &y) → r]. Here, we use a
    condition to test whether the terms at position [{0}] and [{1}] are indeed
    convertible. The rule can only apply if that is the case. Of course we may
    need to check convertibility between more than two terms if a variable has
    more than two occurences. *)
module NLCond : sig
  (** Binary constraint with
      - as {!type:data} a slot of the [vars] array,
      - as {!type:out} a couple of two slots of the [vars] array. *)
  include Cond_sig with
  type exported = int * int and
  type data = int

  (** [constrained i p] tells whether slot [i] is constrained in pool [p]. *)
  val constrained : data -> t -> bool
end = struct
  module IntPairSet = Set.Make(
    struct
      type t = int * int

      let compare : t -> t -> int = fun (i1,i2) (j1,j2) ->
        match i1 - j1 with 0 -> i2 - j2 | k -> k
    end)

  (** A non linearity constraint. *)
  type t =
    { partial : int IntMap.t
    (** An association [(e, v)] is a slot [e] of the [env] array with a slot
        [v] of the [vars] array. *)
    ; available : IntPairSet.t
    (** Pairs of this set are checkable constraints, i.e. the two integers
        refer to available positions in the {!val:vars} array. *) }

  type cond = int * int

  type exported = cond

  type data = int

  let pp_cond oc (i, j) = Format.fprintf oc "(%d,%d)" i j

  let pp oc pool =
    let pp_sep oc _ = Format.pp_print_string oc "; " in
    let pp_int_int oc (i, j) = Format.fprintf oc "@[(%d, %d)@]" i j in
    let pp_partial oc ism =
      Format.fprintf oc "@[partial: %a@]"
        (Format.pp_print_list ~pp_sep pp_int_int) (IntMap.bindings ism)
    in
    let pp_available oc ips =
      Format.fprintf oc "@[available: %a@]"
        (Format.pp_print_list ~pp_sep pp_int_int) (IntPairSet.elements ips)
    in
    Format.fprintf oc "Nl constraints:@,@[<v>%a@,%a@,@]"
      pp_partial pool.partial pp_available pool.available

  let empty = { partial = IntMap.empty ; available = IntPairSet.empty }

  let is_empty c = IntPairSet.is_empty c.available

  let normalize (i, j) = if i < j then (i, j) else (j, i)

  let constrained : data -> t -> bool = fun slot pool ->
    IntMap.mem slot pool.partial

  let is_instantiated pair c = IntPairSet.mem pair c.available

  let remove pair pool =
    { pool with available = IntPairSet.remove pair pool.available }

  let export pair = pair

  let instantiate vslot esl pool =
    try
      let e = normalize (vslot, IntMap.find esl pool.partial) in
      { pool with available = IntPairSet.add e pool.available }
    with Not_found ->
      { pool with partial = IntMap.add esl vslot pool.partial }

  let rec choose pools =
    match pools with
    | p :: t ->
        if IntPairSet.is_empty p.available then choose t else
        Some(IntPairSet.choose p.available)
    | []     -> None
end

(** Free variable constraints to verify which variables are free in a term. If
    there is a rule of the form [f (λ x y, &Y[y]) → &Y], then we need to check
    that the term at position [{0.0}] depends only on free variable [y]. *)
module FVCond : sig
  (** Binary constraint with
      - as {!type:data} an array of free variables,
      - as {!type:out} the slot of the [vars] array and an array of variables
        that may appear free in the term. *)
  include Cond_sig with
  type exported = int * tvar array and
  type data = tvar array
end = struct
  type t = (tvar array) IntMap.t

  type cond = int * tvar array

  type exported = cond

  type data = tvar array

  let pp_cond oc (sl, vars) =
    let pp_sep oc _ = Format.pp_print_string oc "; " in
    Format.fprintf oc "%d: {@[<h>%a@]}" sl
      (Format.pp_print_list ~pp_sep Print.pp_tvar) (Array.to_list vars)

  let pp oc available =
    let pp_sep oc _ = Format.pp_print_string oc "; " in
    let pp_tvs = Format.pp_print_list ~pp_sep Print.pp_tvar in
    let ppit oc (a, b) =
      Format.fprintf oc "@[(%d, %a)@]" a pp_tvs (Array.to_list b)
    in
    Format.fprintf oc "Fv constraints:@,@[<v>@[available: %a@]@,@]@."
      (Format.pp_print_list ppit) (IntMap.bindings available)

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

  let rec choose pools =
    match pools with
    | h :: t ->
        if IntMap.is_empty h then choose t else
        Some(IntMap.choose h)
    | []     -> None
end
