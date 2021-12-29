open Common
open Timed
open Term

let path = Sign.ghost_path "coercion"

let sign : Sign.t =
  let dummy = Sign.dummy () in
  let sign = {dummy with Sign.sign_path = path} in
  Sign.loaded := Path.Map.add path sign !(Sign.loaded);
  sign

let coerce : sym =
  let id = Pos.none "#c" in
  Sign.add_symbol sign Public Defin Eager false id mk_Kind []

let is_ghost s = s == coerce
