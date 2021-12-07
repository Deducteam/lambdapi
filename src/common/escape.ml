(** Management of escaped identifiers ["{|...|}"]. *)

(** [is_escaped s] tells if [s] begins with ["{|"] and ends with ["|}"]
   without overlapping. For efficiency, we just test that it starts with
   ['{']. *)
let is_escaped : string -> bool = fun s -> s <> "" && s.[0] = '{'

(** [unescape s] removes ["{|"] and ["|}"] if [s] is an escaped identifier. *)
let unescape : string -> string = fun s ->
  if is_escaped s then String.(sub s 2 (length s - 4)) else s

(** [p] is assumed to be a regular identifier. If [n] is a regular identifier
   too, then [add_prefix p n] is just [p ^ n]. Otherwise, it is ["{|" ^ p ^
   unescape n ^ "|}"]. *)
let add_prefix : string -> string -> string = fun p n ->
  if is_escaped n then "{|" ^ p ^ unescape n ^ "|}" else p ^ n

(** [s] is assumed to be a regular identifier. If [n] is a regular identifier
   too, then [add_suffix n s] is just [n ^ s]. Otherwise, it is ["{" ^
   unescape n ^ s ^ "|}"]. *)
let add_suffix : string -> string -> string = fun n s ->
  if is_escaped n then "{|" ^ unescape n ^ s ^ "|}"  else n ^ s
