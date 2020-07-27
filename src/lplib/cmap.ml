(*Type of points and intervals. Used to determine if a cursor is in the range
of a specific token, which is an interval of points (positions)*)
(*The presence of t and compare make RangeType an OrderedType (in the sense of Map) *)
module type RangeType = sig

  type point
  val make_point : int -> int -> point

  val line : point -> int
  val column : point -> int
  type cmp = Before | In | After

  val point_to_string : point -> string

  type t
  type interval = t
  (*Ensures an interval is well defined (e.g with start < finish)*)
  val make_interval : point -> point -> interval

  val interval_start : interval -> point
  val interval_end : interval -> point

  val in_range : point -> interval -> cmp

  (*Intervals need to be well defined (i.e returned by make_interval)*)
  val compare : t -> t -> int

  val interval_to_string : interval -> string

end

(*In this implementation, two intervals are considered 
equal if one is included in the other.
This is meant to locate a cursor (which is an interval 
with start = finish) inside an interval

In any other case, overlapping intervals
can't be compared and will throw an error.

An interval is considered "smaller" than another
if all its points are smaller that the points
of the other (i.e its finishing point is before
the starting point of the other)*)
module Range : RangeType = struct

  type point = { l : int; c : int }
  let make_point l c = { l = l; c = c}

  let line pt = pt.l
  let column pt = pt .c
  type cmp = Before | In | After

  let point_to_string pt = "Line : "^(string_of_int pt.l)
  ^"; Column : "^(string_of_int pt.c)^"\n"

  type t = point * point
  type interval = t
  let make_interval x y = 
    assert ( (line x < line y) || (line x = line y && column x <= column y) );
    (x, y)


  let interval_start = fst
  let interval_end = snd


  let in_range pos (pos1, pos2) = 

    if pos.l < pos1.l || (pos.l = pos1.l && pos.c < pos1.c)
    then Before

    else if pos.l > pos2.l || (pos.l = pos2.l && pos.c > pos2.c)
    then After

    else In
  
  let compare (s1, f1) (s2, f2) =

    (*Two intervals are considerd equal if one is included in the other*)
    if (s1 >= s2 && f1 <= f2) || (s1 <= s2 && f1 >= f2)
    then 0

    else if f1 = s2
    then -1

    else if s1 = f2
    then 1

    else
      let f = in_range f1 (s2, f2) in

      if f = Before
      then -1

      else if f = After
      then
        let s = in_range s1 (s2, f2) in

        if s = After
        then 1

        else
          failwith "Intervals overlap, no inclusion between the two"

      else
        failwith "Intervals overlap, no inclusion between the two"

  let interval_to_string interv =
    let s, f = (interval_start interv), (interval_end interv) in
    "From :\n"^(point_to_string s)^"To :\n"^(point_to_string f)
end

(*A structure which maps a position of the cursor to the corresponding token
in a given text editor with a .lp file open*)
module type CursorMapSig = sig

  type 'a t
  type interval
  type point

  (*Adds the range for a token and the token in a map*)
  (*Requires all keys to be non overlapping intervals*)
  (*/!\ Does not ensure consistency if the added keys are overlapping
  intervals, e.g might change a previously added (key, element) couple*)
  val add : interval -> 'a -> 'a t -> 'a t
  (*Given a cursor position, returns the corresponding token*)
  val find : point -> 'a t -> (interval * 'a) option

  val empty : 'a t

  val to_string : ('b * string) t -> string
end

(*The functor for cursor maps*)
module MakeCursorMap (Range : RangeType) = struct

  (*A map of which keys are intervals*)
  module RangeMap = Map.Make(Range)
 
  (*Now we need to transform the map so that :
    - the keys for "add" are intervals
    - the keys for "find" are points
  *)
  type 'a t = (Range.interval * 'a) RangeMap.t
  type interval = Range.interval
  type point = Range.point
  
  let add interv elt map = 
    RangeMap.add interv (interv, elt) map
  
  let point_to_interval : point -> interval =
  fun pt ->
    Range.make_interval pt pt

  let find cursor map =
    let interv = point_to_interval cursor in
    RangeMap.find_opt interv map

  let empty = RangeMap.empty

  let to_string map =

    let f key (_, (_, elt)) str = (Range.interval_to_string key)
    ^"Token : "^elt^"\n\n"^str
    in

    RangeMap.fold f map ""
end

(*For the code to work we need to share constraints *)
module type RangeCursorMapSig = CursorMapSig
  with type point = Range.point
  and type interval = Range.interval

(*The implementation of CursorMap using a functor *)
module CursorMap : RangeCursorMapSig = MakeCursorMap(Range)