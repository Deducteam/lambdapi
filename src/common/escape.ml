(** Escaped identifiers ["{|...|}"]. *)

(*open Debug*)

(** [is_beg_escaped s] tells if [s] starts with ["{|"]. *)
let is_beg_escaped : string -> bool = fun s ->
  let n = String.length s in n > 1 && s.[0] = '{' && s.[1] = '|'

(** [is_end_escaped s] tells if [s] ends with ["|}"]. *)
let is_end_escaped : string -> bool = fun s ->
  let n = String.length s in n > 1 && s.[n-2] = '|' && s.[n-1] = '}'

(** [is_escaped s] tells if [s] begins with ["{|"] and ends with ["|}"]
   without overlapping. *)
let is_escaped : string -> bool = fun s ->
  let n = String.length s in
  n > 3 && s.[0] = '{' && s.[1] = '|' && s.[n-2] = '|' && s.[n-1] = '}'

(** [unescape s] removes ["{|"] and ["|}"] if [s] is an escaped identifier. *)
let unescape : string -> string = fun s ->
  if is_escaped s then String.(sub s 2 (length s - 4)) else s

(** [add_prefix p s] adds the prefix [p] at the beginning of the
    identifier [s]. *)
let add_prefix : string -> string -> string = fun p s ->
  if is_escaped s then "{|" ^ p ^ unescape s ^ "|}" else p ^ s

(** [split c s] returns the list of all (possibly empty) substrings of
   [s] that are delimited by the [c] character, if [c] does not occur in an
   escaped identifier. [s] is assumed to be a well parenthesized (wrt
   escaping) identifier.

   The function's output is specified by the following invariants:
   - The return list is not empty.
   - Concatenating its elements using [c] as separator returns a string equal
     to the input:
     [String.concat (String.make 1 c) (String.split c s) = s].
   - No string in the result contains the [c] character, except in escaped
     identifiers. *)
let split : char -> string -> string list = fun c s ->
  let sc = String.make 1 c in
  let rec fix_split mp m l =
    (*Format.printf "fix_split %a\n%a\n%a\n\n"
        (D.list D.string) mp (D.option D.string) m (D.list D.string) l;*)
    match m, l with
    | None, [] -> List.rev mp
    | Some m, [] -> List.rev (m::mp)
    | None, s::l ->
        if is_beg_escaped s && not (is_end_escaped s)
        then fix_split mp (Some s) l
        else fix_split (s::mp) None l
    | Some m, s::l ->
        if is_end_escaped s then fix_split ((m^sc^s)::mp) None l
        else fix_split mp (Some(m^sc^s)) l
  in fix_split [] None (String.split_on_char c s)

(* unit testing *)
let _ =
  assert
    (is_escaped "{|}" = false
     && is_escaped "{a|}" = false
     && is_escaped "{|a}" = false
     && is_escaped "{||}" = true
     && is_escaped "{|a|}" = true
     && split '.' "{|a.b|}.c.{|d|}" = ["{|a.b|}";"c";"{|d|}"]
     && split '.' "{|tests|}.OK.{|a b|}.c" = ["{|tests|}";"OK";"{|a b|}";"c"])
