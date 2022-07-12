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

- In the hrs format, variable names must be distinct from function symbol
   names. So bound variables are translated into positive integers and pattern
   variables are prefixed by ["$"].

- There is no clash between function symbol names and A, B, L, P because
   function symbol names are fully qualified.

- Function symbol names are fully qualified but ["."] is replaced by ["_"]
   because ["."] cannot be used in identifiers (["."]  is used in lambda
   abstractions).

- Two occurrences of the same pattern variable name may have two different
   arities (in two different rules). So pattern variable names are prefixed by
   the rule number.

TO DO:

- HRS does not accept unicode characters.

- Optim: output only the symbols used in the rules. *)

open Lplib open Base open Extra
open Core open Term
open Common

(** [syms] maps every symbol to a name. *)
let syms = ref SymMap.empty

(** [bvars] is the set of abstracted variables. *)
let bvars = ref IntSet.empty

(** [nb_rules] is the number of rewrite rules. *)
let nb_rules = ref 0

(** [pvars] map every pattern variable name to its arity. *)
let pvars = ref []

(** [sym_name s] translates the symbol name of [s]. *)
let sym_name : sym pp = fun ppf s ->
    out ppf "%a_%s" (List.pp string "_") s.sym_path s.sym_name

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
let pvar : int pp = fun ppf i -> out ppf "$%d_%d" !nb_rules i

(** [add_pvar i k] declares a pvar of index [i] and arity [k]. *)
let add_pvar : int -> int -> unit = fun i k ->
  pvars := (!nb_rules,i,k)::!pvars

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
  if sign != Unif_rule.sign then
    StrMap.iter (fun _ -> rules_of_sym ppf) Timed.(!(sign.sign_symbols))

(** [iterate f sign] applies [f] on [sign] and its dependencies. *)
let iterate : (Sign.t -> unit) -> Sign.t -> unit = fun f sign ->
  let visited = ref Path.Set.empty in
  let rec handle sign =
    visited := Path.Set.add sign.Sign.sign_path !visited;
    f sign;
    let dep path _ =
      if not (Path.Set.mem path !visited) then
        handle (Path.Map.find path Timed.(!Sign.loaded))
    in
    Path.Map.iter dep Timed.(!(sign.sign_deps))
  in handle sign

(** [sign ppf s] translates the Lambdapi signature [s]. *)
let sign : Sign.t pp = fun ppf sign ->
  (* First, generate the rules in a buffer, because it generates data
     necessary for the other sections. *)
  let buf_rules = Buffer.create 1000 in
  let ppf_rules = Format.formatter_of_buffer buf_rules in
  iterate (rules_of_sign ppf_rules) sign;
  Format.pp_print_flush ppf_rules ();
  (* Function for printing the types of function symbols. *)
  let pp_syms : string SymMap.t pp = fun ppf syms ->
    let sym_decl : string pp = fun ppf n -> out ppf "\n%s : t" n in
    let sym_decl _ n = sym_decl ppf n in SymMap.iter sym_decl syms
  in
  (* Function for printing the types of pattern variables. *)
  let pp_pvars : (int * int * int) list pp = fun ppf pvars ->
    let typ : int pp = fun ppf k ->
      for _i=1 to k do string ppf "t -> " done; out ppf "t" in
    let pvar_decl (n,i,k) = out ppf "\n$%d_%d : %a" n i typ k in
    List.iter pvar_decl pvars in
  (* Function for printing the types of abstracted variables. *)
  let pp_bvars : IntSet.t pp = fun ppf bvars ->
    let bvar_decl : int pp = fun ppf n -> out ppf "\n%d : t" n in
    IntSet.iter (bvar_decl ppf) bvars
  in
  (* Finally, generate the whole hrs file. Note that the variables $x, $y and
     $z used in the rules for beta and let cannot clash with user-defined
     pattern variables which are integers. *)
  out ppf "\
(FUN
A : t -> t -> t
L : t -> (t -> t) -> t
P : t -> (t -> t) -> t
B : t -> t -> (t -> t) -> t%a
)
(VAR
$x : t
$y : t -> t
$z : t%a%a
)
(RULES
A(L($x,$y),$z) -> $y($z),
B($x,$z,$y) -> $y($z)%s
)\n" pp_syms !syms pp_pvars !pvars pp_bvars !bvars (Buffer.contents buf_rules)
