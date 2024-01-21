(** This module provides a function to translate a signature to the TRS format
   used in the confluence competition.

   This translation relies on the following fact: if in all rules l --> r of
   the rewrite system both l and r are patterns, then the system is SN
   whenever the first-order system obtained by forgeting about binders also
   termintes. Note that because of this, we consider only termination without
   the beta rule, as its right hand side is not a pattern.

- Lambdapi terms are translated to a TRS over the following base signature:

  A // binary symbol for application

  L // binary symbol for λ

  B // trinary symbol for let

  P // binary symbol for Π

- Function symbols are translated directly by their unqualified names. If a
   function symbol name clashes with the name of a variable, metavariable or
   a symbol declared in the base signature, we prefix it with !. In order to
   do this, we assume that no function symbol starts with !.

TODO:

- For the time being, we translate rules without verifying that the pattern
   condition is always verified. In the future we should only translate the
   fragment of the system that satisfy the pattern confition in both the lhs
   and the rhs.

*)

open Lplib open Base open Extra
open Core open Term

let sanitize_name : string -> string = fun s ->
  (* we considere names starting with '!' as forbiden, so we can
     use it as an escape character to prevent clashes *)
  if s.[0] = '!' then assert false;
  match s with
  | "A" | "L" | "P" | "B" ->
    (* prevents clashes with the names in the base signature *)
    "!" ^ s
  | _ -> s

(** [sym_name s] translates the symbol name of [s]. *)
let sym_name : sym pp = fun ppf s ->
    out ppf "%s" (sanitize_name s.sym_name)

(** [pvar i] translates the pattern variable index [i]. *)
let pvar : int pp = fun ppf i -> out ppf "$%d" i

let max_var : int ref = ref 0

let set_max_var : int -> unit = fun i ->
  max_var := max i !max_var

(** [term ppf t] translates the term [t]. *)
let rec term : term pp = fun ppf t ->
  match unfold t with
  | Meta _ -> assert false
  | Plac _ -> assert false
  | TRef _ -> assert false
  | TEnv _ -> assert false
  | Wild -> assert false
  | Kind -> assert false
  | Type -> assert false
  | Vari _ -> assert false
  | Symb s -> sym_name ppf s
  | Patt(None,_,_) -> assert false
  | Patt(Some i,_,[||]) -> set_max_var i; pvar ppf i
  | Patt(Some i,_,_) -> (* todo: check it's only applied to bound vars*)
    set_max_var i; pvar ppf i
  | Appl(t,u) -> out ppf "A(%a, %a)" term t term u
  | Abst(a,b) ->
    let _, b = Bindlib.unbind b in
    out ppf "L(%a, %a)" term a  term b
  | Prod(a,b) ->
    let _, b = Bindlib.unbind b in
    out ppf "P(%a, %a)" term a  term b
  | LLet(a,t,b) ->
    let _, b = Bindlib.unbind b in
    out ppf "B(%a,%a,%a)" term a term t term b

(** [rule ppf r] translates the pair of terms [r] as a rule. *)
let rule : (term * term) pp = fun ppf (l, r) ->
  out ppf "\n%a -> %a" term l term r

(** [sym_rule ppf s r] translates the sym_rule [r]. *)
let sym_rule : sym -> rule pp = fun s ppf r ->
  let sr = s, r in rule ppf (lhs sr, rhs sr)

(** Translate the rules of symbol [s]. *)
let rules_of_sym : sym pp = fun ppf s ->
  match Timed.(!(s.sym_def)) with
  | Some d -> rule ppf (mk_Symb s, d)
  | None -> List.iter (sym_rule s ppf) Timed.(!(s.sym_rules))

(** Translate the rules of a dependency except if it is a ghost signature. *)
let rules_of_sign : Sign.t pp = fun ppf sign ->
  if sign != Ghost.sign then
    StrMap.iter (fun _ -> rules_of_sym ppf) Timed.(!(sign.sign_symbols))

(** [sign ppf s] translates the Lambdapi signature [s]. *)
let sign : Sign.t pp = fun ppf sign ->
  (* First, generate the rules in a buffer, because it generates data
     necessary for the other sections. *)
  let buf_rules = Buffer.create 1000 in
  let ppf_rules = Format.formatter_of_buffer buf_rules in
  Sign.iterate (rules_of_sign ppf_rules) sign;
  Format.pp_print_flush ppf_rules ();
  let pp_vars : int pp = fun ppf k ->
    for i = 0 to k do out ppf " $%d" i done in
  out ppf "\
(VAR%a)
(RULES%s
)\n" pp_vars !max_var (Buffer.contents buf_rules)
