(** Export a Lambdapi signature to Dedukti. *)

open Lplib open Base open Extra
open Timed
open Common
open Core open Term

let string = Format.pp_print_string

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

let is_ident : string -> bool = fun s ->
  Parsing.DkLexer.is_ident (Lexing.from_string s)

let escape : string pp = fun ppf s -> out ppf "{|%s|}" s

let ident : string pp = fun ppf s ->
  if s = "" then escape ppf s
  else if s.[0] = '{' then string ppf s
  else if is_keyword s then escape ppf s
  else if is_ident s then string ppf s
  else escape ppf s

let current_path = Stdlib.ref []

let path : Path.t pp = fun ppf p ->
  if p <> Stdlib.(!current_path) then
  match p with
  | [] -> ()
  | [_root_path; m] -> out ppf "%a." ident m
  | _ -> assert false

type item =
  | Sym of sym
  | Rule of (Path.t * string * rule)

let pos_of_item : item -> Pos.popt = fun i ->
  match i with
  | Sym s -> s.sym_pos
  | Rule (_,_,r) -> r.rule_pos

let cmp : item cmp = cmp_map (Lplib.Option.cmp Pos.cmp) pos_of_item

let tvar : tvar pp = fun ppf v -> ident ppf (Bindlib.name_of v)
let tevar : tevar pp = fun ppf v -> ident ppf (Bindlib.name_of v)

let rec term : term pp = fun ppf t ->
  match unfold t with
  | Vari v -> tvar ppf v
  | Type -> out ppf "Type"
  | Kind -> assert false
  | Symb s -> out ppf "%a%a" path s.sym_path ident s.sym_name
  | Prod(a,b) ->
    let x,b' = Bindlib.unbind b in
    if Bindlib.binder_constant b then out ppf "(%a -> %a)" term a term b'
    else out ppf "(%a : %a -> %a)" tvar x term a term b'
  | Abst(a,b) ->
    let x,b = Bindlib.unbind b in
    out ppf "(%a : %a => %a)" tvar x term a term b
  | Appl _ ->
    let h, ts = get_args t in
    out ppf "(%a%a)" term h (List.pp (prefix " " term) "") ts
  | LLet(a,t,u) ->
    let x,u = Bindlib.unbind u in
    out ppf "((%a : %a := %a) => %a)" tvar x term a term t term u
  | Patt(_,s,ts) -> out ppf "%a%a" ident s (Array.pp (prefix " " term) "") ts
  | TEnv(te, ts) -> out ppf "%a%a" tenv te (Array.pp (prefix " " term) "") ts
  | TRef _ -> assert false
  | Wild -> assert false
  | Meta _ -> assert false

and tenv : term_env pp = fun ppf te ->
  match te with
  | TE_Vari v -> tevar ppf v
  | TE_Some _ -> assert false
  | TE_None -> assert false

let modifiers : sym -> string list = fun s ->
  let open Stdlib in
  let r = ref [] in
  let add m = r := m::!r in
  if s.sym_opaq then add "thm"
  else begin
    if s.sym_expo = Protec then add "private";
    match s.sym_prop with
    | Const -> ()
    | Injec -> add "injective"
    | AC _ -> add "defac"
    | Defin -> add "def"
    | Assoc _ -> assert false
    | Commu -> assert false
  end;
  !r

let sym_decl : sym pp = fun ppf s ->
  out ppf "%a%a : %a%a.@."
    (List.pp (suffix string " ") "") (modifiers s)
    ident s.sym_name term !(s.sym_type)
    (Option.pp (prefix " :=" term)) !(s.sym_def)

let rule_decl : (Path.t * string * rule) pp = fun ppf (p, n, r) ->
  let xs, rhs = Bindlib.unmbind r.rhs in
  out ppf "[%a] %a%a%a --> %a.@."
    (Array.pp tevar ", ") xs
    path p ident n (List.pp (prefix " " term) "") r.lhs term rhs

let item : item pp = fun ppf item ->
  match item with
  | Sym s -> sym_decl ppf s
  | Rule r -> rule_decl ppf r

let items_of_sign : Sign.t -> item list = fun sign ->
  let add_sym l s = List.insert cmp (Sym s) l
  and add_rule p n l r = List.insert cmp (Rule (p, n, r)) l in
  let add_sign_symbol n s l =
    List.fold_left (add_rule [] n) (add_sym l s) !(s.sym_rules) in
  let add_rules p n rs l = List.fold_left (add_rule p n) l rs in
  let add_sign_dep p map l = StrMap.fold (add_rules p) map l in
  StrMap.fold add_sign_symbol !(sign.sign_symbols)
    (Path.Map.fold add_sign_dep !(sign.sign_deps) [])

let require : Path.t -> _ -> unit = fun p _ ->
  if p != Unif_rule.path then Format.printf "#REQUIRE %a.@." path p

let sign : Sign.t -> unit = fun sign ->
  Path.Map.iter require !(sign.sign_deps);
  Stdlib.(current_path := sign.sign_path);
  List.iter (item Format.std_formatter) (items_of_sign sign)
