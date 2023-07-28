module B = Stdlib.Bytes
include B

(* Taken from bytes.ml in OCaml 4.14.1. *)

external unsafe_get_uint8 : bytes -> int -> int = "%bytes_unsafe_get"
external unsafe_set_uint8 : bytes -> int -> int -> unit = "%bytes_unsafe_set"

(* UTF codecs and validations *)

let dec_invalid = Uchar.utf_decode_invalid
let[@inline] dec_ret n u = Uchar.utf_decode n (Uchar.unsafe_of_int u)

(* In case of decoding error, if we error on the first byte, we
   consume the byte, otherwise we consume the [n] bytes preceeding
   the erroring byte.

   This means that if a client uses decodes without caring about
   validity it naturally replace bogus data with Uchar.rep according
   to the WHATWG Encoding standard. Other schemes are possible by
   consulting the number of used bytes on invalid decodes. For more
   details see https://hsivonen.fi/broken-utf-8/

   For this reason in [get_utf_8_uchar] we gradually check the next
   byte is available rather than doing it immediately after the
   first byte. Contrast with [is_valid_utf_8]. *)

(* UTF-8 *)

let[@inline] not_in_x80_to_xBF b = b lsr 6 <> 0b10
let[@inline] not_in_xA0_to_xBF b = b lsr 5 <> 0b101
let[@inline] not_in_x80_to_x9F b = b lsr 5 <> 0b100
let[@inline] not_in_x90_to_xBF b = b < 0x90 || 0xBF < b
let[@inline] not_in_x80_to_x8F b = b lsr 4 <> 0x8

let[@inline] utf_8_uchar_2 b0 b1 =
  ((b0 land 0x1F) lsl 6) lor
  ((b1 land 0x3F))

let[@inline] utf_8_uchar_3 b0 b1 b2 =
  ((b0 land 0x0F) lsl 12) lor
  ((b1 land 0x3F) lsl 6) lor
  ((b2 land 0x3F))

let[@inline] utf_8_uchar_4 b0 b1 b2 b3 =
  ((b0 land 0x07) lsl 18) lor
  ((b1 land 0x3F) lsl 12) lor
  ((b2 land 0x3F) lsl 6) lor
  ((b3 land 0x3F))

let get_utf_8_uchar b i =
  let b0 = get_uint8 b i in (* raises if [i] is not a valid index. *)
  let get = unsafe_get_uint8 in
  let max = length b - 1 in
  match Char.unsafe_chr b0 with (* See The Unicode Standard, Table 3.7 *)
  | '\x00' .. '\x7F' -> dec_ret 1 b0
  | '\xC2' .. '\xDF' ->
      let i = i + 1 in if i > max then dec_invalid 1 else
      let b1 = get b i in if not_in_x80_to_xBF b1 then dec_invalid 1 else
      dec_ret 2 (utf_8_uchar_2 b0 b1)
  | '\xE0' ->
      let i = i + 1 in if i > max then dec_invalid 1 else
      let b1 = get b i in if not_in_xA0_to_xBF b1 then dec_invalid 1 else
      let i = i + 1 in if i > max then dec_invalid 2 else
      let b2 = get b i in if not_in_x80_to_xBF b2 then dec_invalid 2 else
      dec_ret 3 (utf_8_uchar_3 b0 b1 b2)
  | '\xE1' .. '\xEC' | '\xEE' .. '\xEF' ->
      let i = i + 1 in if i > max then dec_invalid 1 else
      let b1 = get b i in if not_in_x80_to_xBF b1 then dec_invalid 1 else
      let i = i + 1 in if i > max then dec_invalid 2 else
      let b2 = get b i in if not_in_x80_to_xBF b2 then dec_invalid 2 else
      dec_ret 3 (utf_8_uchar_3 b0 b1 b2)
  | '\xED' ->
      let i = i + 1 in if i > max then dec_invalid 1 else
      let b1 = get b i in if not_in_x80_to_x9F b1 then dec_invalid 1 else
      let i = i + 1 in if i > max then dec_invalid 2 else
      let b2 = get b i in if not_in_x80_to_xBF b2 then dec_invalid 2 else
      dec_ret 3 (utf_8_uchar_3 b0 b1 b2)
  | '\xF0' ->
      let i = i + 1 in if i > max then dec_invalid 1 else
      let b1 = get b i in if not_in_x90_to_xBF b1 then dec_invalid 1 else
      let i = i + 1 in if i > max then dec_invalid 2 else
      let b2 = get b i in if not_in_x80_to_xBF b2 then dec_invalid 2 else
      let i = i + 1 in if i > max then dec_invalid 3 else
      let b3 = get b i in if not_in_x80_to_xBF b3 then dec_invalid 3 else
      dec_ret 4 (utf_8_uchar_4 b0 b1 b2 b3)
  | '\xF1' .. '\xF3' ->
      let i = i + 1 in if i > max then dec_invalid 1 else
      let b1 = get b i in if not_in_x80_to_xBF b1 then dec_invalid 1 else
      let i = i + 1 in if i > max then dec_invalid 2 else
      let b2 = get b i in if not_in_x80_to_xBF b2 then dec_invalid 2 else
      let i = i + 1 in if i > max then dec_invalid 3 else
      let b3 = get b i in if not_in_x80_to_xBF b3 then dec_invalid 3 else
      dec_ret 4 (utf_8_uchar_4 b0 b1 b2 b3)
  | '\xF4' ->
      let i = i + 1 in if i > max then dec_invalid 1 else
      let b1 = get b i in if not_in_x80_to_x8F b1 then dec_invalid 1 else
      let i = i + 1 in if i > max then dec_invalid 2 else
      let b2 = get b i in if not_in_x80_to_xBF b2 then dec_invalid 2 else
      let i = i + 1 in if i > max then dec_invalid 3 else
      let b3 = get b i in if not_in_x80_to_xBF b3 then dec_invalid 3 else
      dec_ret 4 (utf_8_uchar_4 b0 b1 b2 b3)
  | _ -> dec_invalid 1

let set_utf_8_uchar b i u =
  let set = unsafe_set_uint8 in
  let max = length b - 1 in
  match Uchar.to_int u with
  | u when u < 0 -> assert false
  | u when u <= 0x007F ->
      set_uint8 b i u;
      1
  | u when u <= 0x07FF ->
      let last = i + 1 in
      if last > max then 0 else
      (set_uint8 b i (0xC0 lor (u lsr 6));
       set b last (0x80 lor (u land 0x3F));
       2)
  | u when u <= 0xFFFF ->
      let last = i + 2 in
      if last > max then 0 else
      (set_uint8 b i (0xE0 lor (u lsr 12));
       set b (i + 1) (0x80 lor ((u lsr 6) land 0x3F));
       set b last (0x80 lor (u land 0x3F));
       3)
  | u when u <= 0x10FFFF ->
      let last = i + 3 in
      if last > max then 0 else
      (set_uint8 b i (0xF0 lor (u lsr 18));
       set b (i + 1) (0x80 lor ((u lsr 12) land 0x3F));
       set b (i + 2) (0x80 lor ((u lsr 6) land 0x3F));
       set b last (0x80 lor (u land 0x3F));
       4)
  | _ -> assert false

let is_valid_utf_8 b =
  let rec loop max b i =
    if i > max then true else
    let get = unsafe_get_uint8 in
    match Char.unsafe_chr (get b i) with
    | '\x00' .. '\x7F' -> loop max b (i + 1)
    | '\xC2' .. '\xDF' ->
        let last = i + 1 in
        if last > max
        || not_in_x80_to_xBF (get b last)
        then false
        else loop max b (last + 1)
    | '\xE0' ->
        let last = i + 2 in
        if last > max
        || not_in_xA0_to_xBF (get b (i + 1))
        || not_in_x80_to_xBF (get b last)
        then false
        else loop max b (last + 1)
    | '\xE1' .. '\xEC' | '\xEE' .. '\xEF' ->
        let last = i + 2 in
        if last > max
        || not_in_x80_to_xBF (get b (i + 1))
        || not_in_x80_to_xBF (get b last)
        then false
        else loop max b (last + 1)
    | '\xED' ->
        let last = i + 2 in
        if last > max
        || not_in_x80_to_x9F (get b (i + 1))
        || not_in_x80_to_xBF (get b last)
        then false
        else loop max b (last + 1)
    | '\xF0' ->
        let last = i + 3 in
        if last > max
        || not_in_x90_to_xBF (get b (i + 1))
        || not_in_x80_to_xBF (get b (i + 2))
        || not_in_x80_to_xBF (get b last)
        then false
        else loop max b (last + 1)
    | '\xF1' .. '\xF3' ->
        let last = i + 3 in
        if last > max
        || not_in_x80_to_xBF (get b (i + 1))
        || not_in_x80_to_xBF (get b (i + 2))
        || not_in_x80_to_xBF (get b last)
        then false
        else loop max b (last + 1)
    | '\xF4' ->
        let last = i + 3 in
        if last > max
        || not_in_x80_to_x8F (get b (i + 1))
        || not_in_x80_to_xBF (get b (i + 2))
        || not_in_x80_to_xBF (get b last)
        then false
        else loop max b (last + 1)
    | _ -> false
  in
  loop (length b - 1) b 0
