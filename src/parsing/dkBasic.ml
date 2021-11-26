(* part of kernel/basic.ml *)

type ident = string

let ident_eq s1 s2 = s1 == s2 || s1 = s2

type mident = string

module WS = Weak.Make (struct
  type t = ident
  let equal = ident_eq
  let hash = Hashtbl.hash
end)

let hash_ident = WS.create 251

let mk_ident = WS.merge hash_ident

let underscore = mk_ident "_"

let hash_mident = WS.create 251

let mk_mident md = WS.merge hash_mident md
