(*Type of points and intervals. Used to determine if a cursor is in the range
of a specific token, which is an interval of points (positions)*)
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

  (*Overlapping intervals can't be compared and will throw an error*)
  (*Intervals need to be well defined (i.e returned by make_interval)*)
  val compare : t -> t -> int

  val interval_to_string : interval -> string

end


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

    if f1 = s2
    then -1

    else if s1 = f2
    then 1

    else if f1 = f2 && s1 = s2
    then 0

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
          failwith "Intervals overlap"

      else
        failwith "Intervals overlap"

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
  type 'a t = 'a RangeMap.t
  type interval = Range.interval
  type point = Range.point
  
  let add interv elt map = 

    if RangeMap.mem interv map
    then failwith "CursorMap.add : tried to insert a token in an already mapped
    interval"

    else RangeMap.add interv elt map
  
  let find cursor map =

    (*Since the key is a cursor but the map is made of intervals,
    we need to find the first interval in the map containing the cursor*)

    (*In order to use find_first_opt, which returns this first interval,
    we need to define a monotonically increasing function that returns false
    given an interval if the cursor is after it, and true otherwise.
    We'll call this function cursor_inbefore.
    
    Monotonically increasing means that if an interval i precedes another
    interval j and cursor_inbefore i returns true, cursor_inbefore j will
    return true (intuitively false < true) *)

    let cursor_inbefore interv = 
      let is_in = Range.in_range cursor interv in
      is_in = In || is_in = Before
    in

    let found = RangeMap.find_first_opt cursor_inbefore map in

    (*Now we need to make sure that we have found the interval the cursor
    is in and not just the smallest interval (in the sense of Range.compare)
    after the cursor *)
    match found with
    |Some(interv, _) ->
        if Range.in_range cursor interv = In
        then found

        else None
    |_ -> found


  let empty = RangeMap.empty

  let to_string map =

    let f key (_, elt) str = (Range.interval_to_string key)
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