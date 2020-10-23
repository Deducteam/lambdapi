module S = Stdlib.String
include S

let to_list : string -> char list =
 fun s ->
  let l = ref [] in
  S.iter (fun c -> l := c :: !l) s;
  List.rev !l

let of_list : char list -> string =
 fun l ->
  let b = Buffer.create 37 in
  List.iter (Buffer.add_char b) l;
  Buffer.contents b

let is_substring : string -> string -> bool =
 fun e s ->
  let len_e = S.length e in
  let len_s = S.length s in
  let rec is_sub i =
    if len_s - i < len_e then false
    else if S.sub s i len_e = e then true
    else is_sub (i + 1)
  in
  is_sub 0

let is_prefix : string -> string -> bool =
 fun p s ->
  let len_p = S.length p in
  let len_s = S.length s in
  len_p <= len_s && S.sub s 0 len_p = p

let for_all : (char -> bool) -> string -> bool =
 fun p s ->
  let len_s = S.length s in
  let rec for_all i = i >= len_s || (p (S.get s i) && for_all (i + 1)) in
  for_all 0
