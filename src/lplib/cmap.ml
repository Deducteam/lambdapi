(**Module for points and intervals. Used to determine if a cursor is in the range
   of a specific token, which is an interval of points (cursor positions).
   The presence of t and compare make RangeType an OrderedType (in the sense of
   Map).
   For now, the useful modules out of this library are Range and RangeMap. *)
module type RangeType =
  sig
    type point type t type interval = t
    
    (**[make_point ln col] creates a point with line [ln] and column [col]. *)
    val make_point : int -> int -> point

    (**[make_interval s e] creates an interval with start [s] and end [e].
       Ensures an interval is well defined (e.g with start < finish). *)
    val make_interval : point -> point -> interval
    val line : point -> int
    val column : point -> int
    val interval_start : interval -> point
    val interval_end : interval -> point

    (**Type for the position of a cursor relative to an interval. *)
    type cmp = Before | In | After
    (**[in_range pt i] returns [Before], [In] or [After] depending on the
       position of the point [pt] relative to the interval [i].*)
    val in_range : point -> interval -> cmp

    (**Comparison over intervals.

       An interval is considered "smaller" than another if its finishing point
       is before the starting point of the other.

       Intervals need to be well defined (i.e returned by make_interval).
       Two intervals are considered equal if one is included in the other. 
       In any other case, overlapping intervals can't be compared and will
       throw an error.
       *)
    val compare : t -> t -> int
    val point_to_string : point -> string
    val interval_to_string : interval -> string

      (**[translate i ds df] returns the interval [i] with its starting point
         translated by [ds] and finishing point translated by [df]. 
         
         Will throw an error if the resulting interval is not well-defined
         (see make_interval). Only translates column-wise,
         does not modify the line coordinates of the extremity points. *)
    val translate : interval -> int -> int -> interval
  end

module Range : RangeType =
  struct
    (**/**)
    type point = { l : int; c : int } type t = point * point type interval = t
    let make_point l c =
      { l = l; c = c}
    let make_interval x y =
      assert (x <= y);
      (x, y)
    let line pt = pt.l
    let column pt = pt .c
    let interval_start = fst
    let interval_end = snd
    type cmp = Before | In | After

    let in_range pos (pos1, pos2) =
      (*Comparison operators work as lexicographic comparison
        on points (meaning l is compared, then c is compared). *)
      if pos < pos1 then Before
      else if pos > pos2 then After
      else In
    
    let compare (s1, f1) (s2, f2) =
      if (s1 >= s2 && f1 <= f2) || (s1 <= s2 && f1 >= f2) then 0
      else if f1 <= s2 then -1
      else if s1 >= f2 then 1
      else failwith "Intervals overlap, no inclusion between the two"
    
    let point_to_string pt =
      "Line : " ^ string_of_int pt.l
      ^ "; Column : " ^ string_of_int pt.c ^ "\n"
    
    let interval_to_string interv =
      let s, f = (interval_start interv), (interval_end interv) in
      "From :\n" ^ point_to_string s ^ "To :\n" ^ point_to_string f

    let translate interv ds df =
      let s = interval_start interv in
      let f = interval_end interv in
      let s2 = make_point (line s) (column s - ds) in
      let f2 = make_point (line f) (column f + df) in
      assert (s2 <= f2);
      make_interval s2 f2
  end


module type RangeMapType =
  sig
    (**Maps a position of the cursor (point) to the corresponding token of type 'a
      in a given text editor with a .lp file open. *)
    type 'a t
    type interval
    type point

    (**[find pt map] returns the only (token, range) couple in map such
       that [pt] is a point within the mapped interval range.
       Requires [map] to be well-defined (see add). *)
    val find : point -> 'a t -> (interval * 'a) option

    (**The empty range map.*)
    val empty : 'a t

    (**[add range token map] adds a mapping (key : [range],
       value : [token]) to [map].

       Requires all added keys to be non overlapping intervals to be well-defined.
       /!\ Does not ensure proper functionning if the added keys are overlapping
       intervals, e.g might change a previously added (key, element) couple
       or throw an error. *)
    val add : interval -> 'a -> 'a t -> 'a t
    val to_string : ('a -> string) -> 'a t -> string
  end

(*The functor for cursor maps. *)
module MakeRangeMap (Range : RangeType) =
  struct
    (*A map of which keys are intervals. *)
    module RangeMap = Map.Make(Range)
    (*Now we need to transform the map so that :
      - the keys for "add" are intervals
      - the keys for "find" are points.
    *)
    type 'a t = (Range.interval * 'a) RangeMap.t
    type interval = Range.interval
    type point = Range.point

    let point_to_interval : point -> interval = fun pt ->
      Range.make_interval pt pt

    let find cursor map =
      let interv = point_to_interval cursor in
      RangeMap.find_opt interv map

    let empty = RangeMap.empty

    let add interv elt map =
      RangeMap.add interv (interv, elt) map

    let to_string elt_to_string (map : 'a t) =
      let f key elt str =
        let (_, e) = elt in
        Range.interval_to_string key
        ^ "Token : " ^ elt_to_string e ^ "\n\n" ^ str
      in
      RangeMap.fold f map ""
  end

(*For the code to work we need to share constraints. *)
module type SharedRangeMapType = RangeMapType
  with type point = Range.point
  and type interval = Range.interval

(*The implementation of CursorMap using a functor. *)
module RangeMap : SharedRangeMapType = MakeRangeMap(Range)