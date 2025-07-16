(** Export a Lambdapi signature to Dedukti. *)

open Lplib open Base open Extra
open Timed
open Common
open Core open Term

(** Translation of identifiers. Lambdapi identifiers that are Dedukti keywords
   or invalid Dedukti identifiers are escaped, a feature offered by
   Dedukti. *)

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

let is_mident : string -> bool = fun s ->
  Parsing.DkLexer.is_mident (Lexing.from_string s)

(*let replace_spaces : string -> string = fun s ->
  let open Bytes in
  let b = of_string s in
  for i=0 to length b - 1 do
    match get b i with
    | ' ' | '\n' -> set b i '_'
    | _ -> ()
  done;
  to_string b*)

let ident : string pp = fun ppf s ->
  string ppf
    (if s = "" then Escape.escape s
     else if s.[0] = '{' then s
     else if is_keyword s then Escape.escape s
     else if is_ident s then s
     else Escape.escape s)

(** Translation of paths. Paths equal to the [!current_path] are not
   printed. Non-empty paths end with a dot. We assume that the module p1.p2.p3
   is in the file p1_p2_p3.dk. *)

let path_elt : string pp = fun ppf s ->
  string ppf (if Escape.is_escaped s then Escape.unescape s else s)

let current_path = Stdlib.ref []

let path : Path.t pp = fun ppf p ->
  if p <> Stdlib.(!current_path) then
  match p with
  | [] -> ()
  | p ->
      let m = Format.asprintf "%a" (List.pp path_elt "_") p in
      let m = if is_mident m then m else Escape.escape m in
      out ppf "%s." m

let qid : (Path.t * string) pp = fun ppf (p, i) ->
  out ppf "%a%a" path p ident i

(** Type of Dedukti declarations. *)
type decl =
  | Sym of sym
  | Rule of (Path.t * string * rule)

(** Declarations are ordered wrt their positions in the source. *)

let pos_of_decl : decl -> Pos.popt = fun i ->
  match i with
  | Sym s -> s.sym_pos
  | Rule (_,_,r) -> r.rule_pos

let cmp : decl cmp = cmp_map (Lplib.Option.cmp Pos.cmp) pos_of_decl

(** Translation of terms. *)

let var : var pp = fun ppf v -> string ppf (uniq_name v)

let patt : int pp = fun ppf i -> out ppf "x%d" i

(** [term b ppf t] prints term [t]. Print abstraction domains if [b]. *)
let rec term : bool -> term pp = fun b ppf t ->
  match unfold t with
  | Vari v -> var ppf v
  | Type -> out ppf "Type"
  | Kind -> assert false
  | Symb s -> qid ppf (s.sym_path, s.sym_name)
  | Prod(t,u) ->
    let x,u' = unbind u in
    if binder_occur u
    then out ppf "(%a : %a -> %a)" var x (term b) t (term b) u'
    else out ppf "(%a -> %a)" (term b) t (term b) u'
  | Abst(t,u) ->
    let x,u = unbind u in
    if b then out ppf "(%a : %a => %a)" var x (term b) t (term b) u
    else out ppf "(%a => %a)" var x (term b) u
  | Appl _ ->
    let h, ts = get_args t in
    out ppf "(%a%a)" (term b) h (List.pp (prefix " " (term b)) "") ts
  | LLet(a,t,u) ->
    let x,u = unbind u in
    out ppf "((%a : %a := %a) => %a)" var x (term b) a (term b) t (term b) u
  | Patt(None,_,_) -> assert false
  | Patt(Some i,_,[||]) -> patt ppf i
  | Patt(Some i,_,ts) ->
    out ppf "(%a%a)" patt i (Array.pp (prefix " " (term b)) "") ts
  | Bvar _ -> assert false
  | TRef _ -> assert false
  | Wild -> assert false
  | Meta _ -> assert false
  | Plac _ -> assert false

(** Translation of declarations. *)

let modifiers : sym -> string list = fun s ->
  let open Stdlib in
  let r = ref [] in
  let add m = r := m::!r in
  begin
    match s.sym_prop with
    | Const -> ()
    | Injec -> add "injective"
    | AC _ -> add "defac"
    | Defin -> add "def"
    | Assoc _ -> assert false
    | Commu -> assert false
  end;
  if s.sym_expo = Protec then add "private";
  !r

let sym_decl : sym pp = fun ppf s ->
  match !(s.sym_def) with
  | None ->
    begin match s.sym_prop with
      | AC _ ->
        begin match unfold !(s.sym_type) with
          | Prod(t,_) ->
            out ppf "%a%a [%a].@."
              (List.pp (suffix string " ") "") (modifiers s)
              ident s.sym_name (term true) t
          | _ -> assert false
        end
      | _ ->
        out ppf "%a%a : %a.@."
          (List.pp (suffix string " ") "") (modifiers s)
          ident s.sym_name (term true) !(s.sym_type)
    end
  | Some d ->
    if !(s.sym_opaq) then
      out ppf "thm %a : %a := %a.@."
        ident s.sym_name (term true) !(s.sym_type) (term true) d
    else
      out ppf "%a%a : %a := %a.@."
        (List.pp (suffix string " ") "") (modifiers s)
        ident s.sym_name (term true) !(s.sym_type) (term true) d

let rule_decl : (Path.t * string * rule) pp = fun ppf (p, n, r) ->
  let rec var ppf i =
    if i < 0 then ()
    else if i = 0 then patt ppf 0
    else out ppf "%a,%a" var (i-1) patt i
  in
  out ppf "[%a] %a%a --> %a.@." var (r.vars_nb - 1) qid (p, n)
    (List.pp (prefix " " (term false)) "") r.lhs (term true) r.rhs

let decl : decl pp = fun ppf decl ->
  match decl with
  | Sym s -> sym_decl ppf s
  | Rule r -> rule_decl ppf r

(** [decls_of_sign sign] computes a list of declarations for the
   signature [sign], in order of appearance in the source. *)
let decls_of_sign : Sign.t -> decl list = fun sign ->
  let add_sym l s = List.insert cmp (Sym s) l
  and add_rule p n l r =
    if p = Sign.Ghost.path then l
    else List.insert cmp (Rule (p, n, r)) l
  in
  let add_sign_symbol n s l =
    List.fold_left (add_rule [] n) (add_sym l s) !(s.sym_rules) in
  let add_rules p n sd l = List.fold_left (add_rule p n) l sd.Sign.rules in
  let add_sign_dep p d l = StrMap.fold (add_rules p) d.Sign.dep_symbols l in
  StrMap.fold add_sign_symbol !(sign.sign_symbols)
    (Path.Map.fold add_sign_dep !(sign.sign_deps) [])

(** Translation of a signature. *)

let require : Path.t -> _ -> unit = fun p _ ->
  if p <> Sign.Ghost.path then Format.printf "#REQUIRE %a@." path p

let sign : Sign.t -> unit = fun sign ->
  Path.Map.iter require !(sign.sign_deps);
  Stdlib.(current_path := sign.sign_path);
  List.iter (decl Format.std_formatter) (decls_of_sign sign)
