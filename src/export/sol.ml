(** This module provides a function to translate a signature to the format
   used by the SOL confluence and termination checker.
   @see <https://github.com/hamana55/sol>

SOL allowed identifiers for types, function symbols, bound variables, rule
names:
- [0-9][a-zA-Z0-9_^'-!%/]*
- <[a-zA-Z0-9_^'-*+!%/]+
- [a-z_-%][a-zA-Z0-9_^'-*+!%/]+

SOL allowed identifiers for metavariables:
- [A-Z][a-zA-Z0-9_^'-*!%/<>]*
*)

open Lplib open Base open Extra
open Core open Term

(** [syms] contains the set of symbols used in rules. *)
let syms = ref SymSet.empty

(** [add_sym s] add [s] in [!syms] and [!eqths] if it has axioms. *)
let add_sym : sym -> unit = fun s -> syms := SymSet.add s !syms

(** [sym s] translates the symbol [s]. *)
let sym : sym pp = fun ppf s ->
  out ppf "%a_%s" (List.pp string "_") s.sym_path s.sym_name

(** [bvar v] translates the bound variable [v]. *)
let bvar : tvar pp = fun ppf v -> out ppf "x%d" (Bindlib.uid_of v)

(** [pvar i] translates the pattern variable of index [i]. *)
let pvar : int pp = fun ppf i -> out ppf "M%d" i

(** [term ppf t] translates the term [t]. *)
let rec term : term pp = fun ppf t ->
  match get_args t with
  | Symb s, [] -> add_sym s; sym ppf s
  | Symb s, ts -> add_sym s; out ppf "%a(%a)" sym s (List.pp term ",") ts
  | _ -> raw_term ppf t

and raw_term : term pp = fun ppf t ->
  match unfold t with
  | Meta _ -> assert false
  | Plac _ -> assert false
  | TRef _ -> assert false
  | TEnv _ -> assert false
  | Wild -> assert false
  | Kind -> assert false
  | Type -> assert false
  | Vari v -> bvar ppf v
  | Symb _ -> assert false
  | Patt(None,_,_) -> assert false
  | Patt(Some i,_,[||]) -> pvar ppf i
  | Patt(Some i,_,ts) ->
    let k = Array.length ts in
    let args ppf ts = for i=1 to k-1 do out ppf ",%a" term ts.(i) done in
    out ppf "%a[%a%a]" pvar i term ts.(0) args ts
  | Appl(t,u) -> out ppf "app(%a,%a)" term t term u
  | Abst(_,b) ->
    let x, b = Bindlib.unbind b in out ppf "(%a.%a)" bvar x term b
  | Prod _ -> assert false
  | LLet _ -> assert false

(** [rule ppf r] translates the pair of terms [r] as a rule. *)
let rule : (term * term) pp =
  let rule_nb = ref 0 in
  fun ppf (l, r) ->
  incr rule_nb; out ppf "\n  (rule%d) %a => %a" !rule_nb term l term r

(** [sym_rule s ppf r] translates the sym_rule [s,r]. *)
let sym_rule : sym -> rule pp = fun s ppf r ->
  let sr = s, r in rule ppf (lhs sr, rhs sr)

(** Translate the rules of symbol [s]. *)
let rules_of_sym : sym pp = fun ppf s ->
  match Timed.(!(s.sym_def)) with
  | Some d -> rule ppf (mk_Symb s, d)
  | None -> List.iter (sym_rule s ppf) Timed.(!(s.sym_rules))

(** Translate the rules of a signature except if it is a ghost signature. *)
let rules_of_sign : Sign.t pp = fun ppf sign ->
  if sign != Ghost.sign then
    StrMap.iter (fun _ -> rules_of_sym ppf) Timed.(!(sign.sign_symbols))

(** [typ ppf t] translates the type [t]. *)
let rec typ : term pp = fun ppf t ->
  match unfold t with
  | Prod(a,b) ->
      if Bindlib.binder_constant b then
        let _,b = Bindlib.unbind b in
        out ppf "(%a -> %a)" typ a typ b
      else assert false
  | Symb s -> sym ppf s
  | _ -> assert false

(** [typ_decl t] translates the term [t] as a type declaration. *)
let rec typ_decl : term pp = fun ppf t ->
  match unfold t with
  | Prod(a,b) ->
      if Bindlib.binder_constant b then
        let _,b = Bindlib.unbind b in
        out ppf "%a%a" typ a codomain b
      else assert false
  | Symb s -> sym ppf s
  | _ -> assert false

and codomain : term pp = fun ppf t ->
  match unfold t with
  | Prod(a,b) ->
      if Bindlib.binder_constant b then
        let _,b = Bindlib.unbind b in
        out ppf ", %a%a" typ a codomain b
      else assert false
  | Symb s -> out ppf " -> %a" sym s
  | _ -> assert false

(** [sign ppf s] translates the Lambdapi signature [s]. *)
let sign : Sign.t pp = fun ppf sign ->
  (* First, generate the rules in a buffer, because it generates data
     necessary for the other sections. *)
  let buf_rules = Buffer.create 1000 in
  let ppf_rules = Format.formatter_of_buffer buf_rules in
  Sign.iterate (rules_of_sign ppf_rules) sign;
  Format.pp_print_flush ppf_rules ();
  (* Function for declaring the types of function symbols. *)
  let pp_syms : SymSet.t pp = fun ppf syms ->
    let sym_decl : sym pp = fun ppf s ->
      out ppf "\n  %a : %a" sym s typ_decl Timed.(!(s.sym_type)) in
    SymSet.iter (sym_decl ppf) syms
  in
  (* Function for declaring the axioms of function symbols. *)
  let pp_axioms : SymSet.t pp = fun ppf syms ->
    let rec prop s ppf p =
      match p with
      | Commu -> out ppf "\n  (%a_com) %a(X,Y) = %a(Y,X)" sym s sym s sym s
      | Assoc _ ->
          out ppf "\n  (%a_assoc) %a(%a(X,Y),Z) = %a(X,%a(Y,Z))"
            sym s sym s sym s sym s sym s
      | AC _ -> prop s ppf Commu; prop s ppf (Assoc true)
      | _ -> ()
    in
    SymSet.iter (fun s -> prop s ppf s.sym_prop) syms
  in
  out ppf "\
sig = [signature|
  app : (a -> b), a -> b%a
|]
rules = [rule|
  (beta) app(x.M[x],N) => M[N]%s
|]
axioms = [axiom|%a
|]\n" pp_syms !syms (Buffer.contents buf_rules) pp_axioms !syms
