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

(* Taken from string.ml in OCaml 4.14.1. *)
module B = Bytes
let bos = B.unsafe_of_string
let get_utf_8_uchar s i = B.get_utf_8_uchar (bos s) i
let is_valid_utf_8 s = B.is_valid_utf_8 (bos s)

(* [string_of_file f] puts the contents of file [f] in a string. *)
let string_of_file f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  Bytes.to_string s

let is_string_literal (s:string): bool =
  let n = S.length s in n >= 2 && S.get s 0 = '"' && S.get s (n-1) = '"'

let remove_quotes (n:string): string = S.sub n 1 (S.length n - 2)
