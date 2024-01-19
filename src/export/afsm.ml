(** This module provides a function to translate a signature to the AFSM
   format used by the Wanda termination checker. Note that because
   termination is checked at the untyped level, Wanda will *always* answer NO,
   as we have an untyped beta rule. However, by removing the beta rule we can
   sometimes show termination of the rest of the system. This can be useful
   when showing confluence of the system: by Von Oostrom's orthogonal
   combinations criterion, if the system without beta is confluent, then by
   combining it with beta it stays confluent. Thus, if the system without beta
   is weakly confluent, then by checking its termination we can deduce the
   confluence of the system with beta.

- Lambdapi terms are translated to terms over the following base signature:

  A : t -> t -> t // for application

  L : t -> (t -> t) -> t // for λ

  B : t -> t -> (t -> t) -> t // for let

  P : t -> (t -> t) -> t // for Π

Function symbols and variables are translated as symbols of type t.

Pattern variables of arity n are translated as variables of type t -> ... -> t
   with n times ->.

- In the afsm format, variable names must be distinct from function symbol
   names. So bound variables are translated into positive integers and pattern
   variables are translated as XiNj where i is the number of the rule and j
   is the indice of the variable. Function symbols are translated directly
   by their unqualified names. If a function symbol name clashes with the
   name of a variable, metavariable or a symbol declared in the base
   signature, we prefix it with !. In order to do this, we assume that no
   function symbol starts with !.

- Unicode is translated as unicode, and Wanda does not accept it. We chose not
   to implement a translation to their codes, as the output would be
   unreadable. In this case, it is better if the user removes manually the
   unicode from their file, this way they can chose a more readable
   replacement for the occuring unicode characters.
 *)

open Lplib open Base open Extra
open Core open Term

(** [syms] maps every symbol to a name. *)
let syms = ref SymMap.empty

(** [nb_rules] is the number of rewrite rules. *)
let nb_rules = ref 0

let sanitize_name : string -> string = fun s ->
  (* we considere names starting with '!' as forbiden, so we can
     use it as an escape character to prevent clashes *)
  if s.[0] = '!' then assert false;
  match s with
  | "A" | "L" | "P" | "B" ->
    (* prevents clashes with the names in the base signature *)
    "!" ^ s
  | _ ->
    (* prevent clashes metavariable names *)
    if s.[0] = 'X' then "!" ^ s
    (* prevent clashes with variable names, which are just numbers *)
    else if Str.string_match (Str.regexp "[0-9]+$") s 0 then "!" ^ s
    else s (* ok names *)

(** [sym_name s] translates the symbol name of [s]. *)
let sym_name : sym pp = fun ppf s ->
    out ppf "%s" (sanitize_name s.sym_name)

(** [add_sym] declares a Lambdapi symbol. *)
let add_sym : sym -> unit = fun s ->
  syms := SymMap.add s (Format.asprintf "%a" sym_name s) !syms

(** [sym ppf s] translates the Lambdapi symbol [s]. *)
let sym : sym pp = fun ppf s -> string ppf (SymMap.find s !syms)

(** [bvar v] translates the Lambdapi variable [v]. *)
let bvar : tvar pp = fun ppf v -> int ppf (Bindlib.uid_of v)

(** [pvar i] translates the pattern variable index [i]. *)
let pvar : int pp = fun ppf i -> out ppf "X%dN%d" !nb_rules i

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
  | Vari v -> bvar ppf v
  | Symb s -> add_sym s; sym ppf s
  | Patt(None,_,_) -> assert false
  | Patt(Some i,_,[||]) -> pvar ppf i
  | Patt(Some i,_,ts) ->
    let k = Array.length ts in
    let args ppf ts = for i=1 to k-1 do out ppf ",%a" term ts.(i) done in
    out ppf "%a[%a%a]" pvar i term ts.(0) args ts
  | Appl(t,u) -> out ppf "A %a %a" term_safe t term_safe u
  | Abst(a,b) ->
    let x, b = Bindlib.unbind b in
    out ppf "L %a (/\\%a.%a)" term_safe a bvar x term b
  | Prod(a,b) ->
    let x, b = Bindlib.unbind b in
    out ppf "P %a (/\\%a.%a)" term_safe a bvar x term b
  | LLet(a,t,b) ->
    let x, b = Bindlib.unbind b in
    out ppf "B %a %a (/\\%a.%a)" term_safe a term_safe t bvar x term b
and term_safe : term pp = fun ppf t ->
  match unfold t with
  | Vari v -> bvar ppf v
  | Symb s -> add_sym s; sym ppf s
  | Patt(Some i,_,[||]) -> pvar ppf i
  | Patt(Some i,_,ts) ->
    let k = Array.length ts in
    let args ppf ts = for i=1 to k-1 do out ppf ",%a" term ts.(i) done in
    out ppf "%a[%a%a]" pvar i term ts.(0) args ts
  | _ -> out ppf "(%a)" term t

(** [rule ppf r] translates the pair of terms [r] as a rule. *)
let rule : (term * term) pp = fun ppf (l, r) ->
  out ppf "\n%a => %a" term l term r

(** [sym_rule ppf s r] increases the number of rules and translates the
   sym_rule [r]. *)
let sym_rule : sym -> rule pp = fun s ppf r ->
  incr nb_rules; let sr = s, r in rule ppf (lhs sr, rhs sr)

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
  (* Function for printing the types of function symbols. *)
  let pp_syms : string SymMap.t pp = fun ppf syms ->
    let sym_decl : string pp = fun ppf n -> out ppf "\n%s : t" n in
    let sym_decl _ n = sym_decl ppf n in SymMap.iter sym_decl syms
  in
  out ppf "\
A : t -> t -> t
L : t -> (t -> t) -> t
P : t -> (t -> t) -> t
B : t -> t -> (t -> t) -> t%a

A (L V Y) Z => Y Z
B V Z Y => Y Z%s
\n" pp_syms !syms (Buffer.contents buf_rules)
