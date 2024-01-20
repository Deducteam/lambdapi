(** This module provides a function to translate a signature to the HRS format
   used in the confluence competition.

    @see <http://project-coco.uibk.ac.at/problems/hrs.php>.

- Lambdapi terms are translated to the following HRS term algebra with a
   unique type t:

  A : t -> t -> t // for application

  L : t -> (t -> t) -> t // for λ

  B : t -> t -> (t -> t) -> t // for let

  P : t -> (t -> t) -> t // for Π

Function symbols and variables are translated as symbols of type t.

Pattern variables of arity n are translated as variables of type t -> ... -> t
   with n times ->.

- Bound variables are translated into positive integers and pattern
   variables are translated as XiNj where i is the number of the rule and j
   is the indice of the variable. Function symbols are translated directly
   by their unqualified names. If a function symbol name clashes with the
   name of a variable, metavariable or a symbol declared in the base
   signature, we prefix it with !. In order to do this, we assume that no
   function symbol starts with !.

- Two occurrences of the same pattern variable name may have two different
   arities (in two different rules). So pattern variable names are prefixed by
   the rule number.

TO DO:

- Optim: output only the symbols used in the rules. *)

open Lplib open Base open Extra
open Core open Term

(** [syms] maps every symbol to a name. *)
let syms = ref SymMap.empty

(** [bvars] is the set of abstracted variables. *)
let bvars = ref IntSet.empty

(** [nb_rules] is the number of rewrite rules. *)
let nb_rules = ref 0

(** [pvars] map every pattern variable name to its arity. *)
module V = struct
  type t = int * int
  let compare = lex Int.compare Int.compare
end
module VMap = Map.Make(V)
let pvars = ref VMap.empty

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

(** [add_bvar v] declares an abstracted Lambdapi variable. *)
let add_bvar : tvar -> unit = fun v ->
  bvars := IntSet.add (Bindlib.uid_of v) !bvars

(** [bvar v] translates the Lambdapi variable [v]. *)
let bvar : tvar pp = fun ppf v -> int ppf (Bindlib.uid_of v)

(** [pvar i] translates the pattern variable index [i]. *)
let pvar : int pp = fun ppf i -> out ppf "X%dN%d" !nb_rules i

(** [add_pvar i k] declares a pvar of index [i] and arity [k]. *)
let add_pvar : int -> int -> unit = fun i k ->
  pvars := VMap.add (!nb_rules,i) k !pvars

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
  | Patt(Some i,_,[||]) -> add_pvar i 0; pvar ppf i
  | Patt(Some i,_,ts) ->
    let k = Array.length ts in add_pvar i k;
    let args ppf ts = for i=1 to k-1 do out ppf ",%a" term ts.(i) done in
    out ppf "%a(%a%a)" pvar i term ts.(0) args ts
  | Appl(t,u) -> out ppf "A(%a,%a)" term t term u
  | Abst(a,b) ->
    let x, b = Bindlib.unbind b in add_bvar x;
    out ppf "L(%a,\\%a.%a)" term a bvar x term b
  | Prod(a,b) ->
    let x, b = Bindlib.unbind b in add_bvar x;
    out ppf "P(%a,\\%a.%a)" term a bvar x term b
  | LLet(a,t,b) ->
    let x, b = Bindlib.unbind b in add_bvar x;
    out ppf "B(%a,%a,\\%a.%a)" term a term t bvar x term b

(** [rule ppf r] translates the pair of terms [r] as a rule. *)
let rule : (term * term) pp = fun ppf (l, r) ->
  out ppf ",\n%a -> %a" term l term r

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
  (* Function for printing the types of pattern variables. *)
  let pp_pvars = fun ppf pvars ->
    let typ : int pp = fun ppf k ->
      for _i=1 to k do string ppf "t -> " done; out ppf "t" in
    let pvar_decl (n,i) k = out ppf "\nX%dN%d : %a" n i typ k in
    VMap.iter pvar_decl pvars in
  (* Function for printing the types of abstracted variables. *)
  let pp_bvars : IntSet.t pp = fun ppf bvars ->
    let bvar_decl : int pp = fun ppf n -> out ppf "\n%d : t" n in
    IntSet.iter (bvar_decl ppf) bvars
  in
  (* Finally, generate the whole hrs file. *)
  out ppf "\
(FUN
A : t -> t -> t
L : t -> (t -> t) -> t
P : t -> (t -> t) -> t
B : t -> t -> (t -> t) -> t%a
)
(VAR
X0 : t
X1 : t -> t
X2 : t%a%a
)
(RULES
A(L(X0,X1),X2) -> X1(X2),
B(X0,X2,X1) -> X1(X2)%s
)\n" pp_syms !syms pp_pvars !pvars pp_bvars !bvars (Buffer.contents buf_rules)
