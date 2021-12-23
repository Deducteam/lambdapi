(** Export a Lambdapi signature to Dedukti. *)

open Lplib.Base
open Common
open Core
open Timed
open Term
open Lplib.Extra

(** Dedukti keywords. *)
let keyword_table = Hashtbl.create 59

let is_keyword : string -> bool = Hashtbl.mem keyword_table

let _ = let open Parsing.DkTokens in
  let loc = Lexing.dummy_pos, Lexing.dummy_pos in
  List.iter (fun (s, t) -> Hashtbl.add keyword_table s t)
    [ ".", DOT
    ; ",", COMMA
    ; ":", COLON
    ; "==", EQUAL
    ; "[", LEFTSQU
    ; "]", RIGHTSQU
    ; "{", LEFTBRA
    ; "}", RIGHTBRA
    ; "(", LEFTPAR
    ; ")", RIGHTPAR
    ; "-->", LONGARROW
    ; "->", ARROW
    ; "=>", FATARROW
    ; ":=", DEF
    ; "_", UNDERSCORE loc
    ; "Type", TYPE loc
    ; "def", KW_DEF loc
    ; "defac", KW_DEFAC loc
    ; "defacu", KW_DEFACU loc
    ; "injective", KW_INJ loc
    ; "thm", KW_THM loc
    ; "private", KW_PRV loc
    ; "#NAME", NAME (loc, "")
    ; "#REQUIRE", REQUIRE (loc, "")
    ; "#EVAL", EVAL loc
    ; "#INFER", INFER loc
    ; "#CHECK", CHECK loc
    ; "#CHECKNOT", CHECKNOT loc
    ; "#ASSERT", ASSERT loc
    ; "#ASSERTNOT", ASSERTNOT loc
    ; "#PRINT", PRINT loc
    ; "#GDT", GDT loc]

let string = Format.pp_print_string

let is_ident : string -> bool = fun s ->
  Parsing.DkLexer.is_ident (Lexing.from_string s)

let escape : string pp = fun ppf s -> out ppf "{|%s|}" s

let ident : string pp = fun ppf s ->
  if s = "" then escape ppf s
  else if s.[0] = '{' then string ppf s
  else if is_keyword s then escape ppf s
  else if is_ident s then string ppf s
  else escape ppf s

let path : Path.t pp = fun ppf p ->
  match p with
  | [_root_path; m] -> out ppf "%s" m
  | _ -> assert false

let require : Path.t -> 'a -> unit = fun p _ ->
  Format.printf "#REQUIRE %a." path p

type item = Sym of sym | Rule of rule

let items_of_sign : Sign.t -> item list = fun sign ->
  let _add_sym sym items = Sym sym :: items
  and _add_rule rule items = Rule rule :: items in
  let add_sign_symbol _name (_sym, _pos) items = items
  in
  let add_sign_dep _path _map items = items
  in
  StrMap.fold add_sign_symbol !(sign.sign_symbols)
    (Path.Map.fold add_sign_dep !(sign.sign_deps) [])

let sign : Sign.t -> unit = fun s ->
  Path.Map.iter require !(s.sign_deps)
