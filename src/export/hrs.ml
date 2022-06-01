(** This module provides a function to translate a signature to the HRS format
   used in the confluence competition.

    @see <http://project-coco.uibk.ac.at/problems/hrs.php>.

- Lambdapi terms are translated to the following HRS term algebra with a
   unique type "term":

  lam : term -> (term -> term) -> term

  app : term -> term -> term

  pi : term -> (term -> term) -> term

Function symbols and variables are translated as symbols of type term.

Pattern variables of arity n are translated as variables of type term ->
   ... -> term with n times ->.

- In the hrs format, variable names must be distinct from function symbol
   names. So bound variables are translated into positive integers and pattern
   variables are prefixed by ["$"].

- Clashes between function symbol names and lam, app and pi?

- Function symbol names are fully qualified but ["."] is replaced by ["_"]
   because ["."] cannot be used in identifiers (["."]  is used in lambda
   abstractions).

- Do HRS accept unicode characters?

- Two occurrences of the same pattern variable name may have two different
   ariies (in two different rules). So pattern variable names are prefixed by
   the rule number.

TO FIX:

- Translate let by beta-redex or new symbol.

- Optim: do not generate the list of dependencies but iterate over them.

- Optim: output only the symbols used in the rules *)

open Lplib open Base open Extra
open Core open Term

let sym_name = ref SymMap.empty
let bvars = ref IntSet.empty
let nb_rules = ref 0
let pvars = ref StrMap.empty

let reset : unit -> unit = fun () ->
  sym_name := SymMap.empty;
  bvars := IntSet.empty;
  nb_rules := 0;
  pvars := StrMap.empty

let add_sym : sym -> unit =
  let sym : sym pp = fun ppf s ->
    out ppf "%a_%s" (List.pp string "_") s.sym_path s.sym_name
  in fun s ->
  sym_name := SymMap.add s (Format.asprintf "%a" sym s) !sym_name

(** [sym ppf s] outputs the symbol [s] to [ppf]. *)
let sym : sym pp = fun ppf s -> string ppf (SymMap.find s !sym_name)

let add_var : tvar -> unit = fun v ->
  bvars := IntSet.add (Bindlib.uid_of v) !bvars

let var : tvar pp = fun ppf v -> int ppf (Bindlib.uid_of v)

let patt : string pp = fun ppf n -> out ppf "$%d_%s" !nb_rules n

let add_patt : string -> int -> unit = fun n k ->
  pvars := StrMap.add (Format.asprintf "%a" patt n) k !pvars

(** [term ppf p] outputs the term [t] to [ppf]. *)
let rec term : term pp = fun ppf t ->
  match unfold t with
  | Meta _ -> assert false
  | Plac _ -> assert false
  | TRef _ -> assert false
  | TEnv _ -> assert false
  | Wild -> assert false
  | Kind -> assert false
  | Type -> assert false
  | Vari v -> var ppf v
  | Symb s -> add_sym s; sym ppf s
  | Patt(_,n,[||]) -> add_patt n 0; patt ppf n
  | Patt(_,n,ts) ->
    add_patt n (Array.length ts);
    let args ppf ts =
      for i=1 to Array.length ts - 1 do out ppf ",%a" term ts.(i) done in
    out ppf "%a(%a%a)" patt n term ts.(0) args ts
  | Appl(t,u) -> out ppf "app(%a,%a)" term t term u
  | Abst(a,b) ->
    let x, b = Bindlib.unbind b in add_var x;
    out ppf "lam(%a,\\%a.%a)" term a var x term b
  | Prod(a,b)    ->
    let x, b = Bindlib.unbind b in add_var x;
    out ppf "pi(%a,\\%a.%a)" term a var x term b
  | LLet(_,t,u) -> term ppf (Bindlib.subst u t)  (*FIXME*)

(** [rule ppf r] outputs the pair of terms [r] to [ppf]. *)
let rule : (term * term) pp = fun ppf (l, r) ->
  out ppf ",\n%a -> %a" term l term r

(** [sym_rule ppf s r] outputs the rule [r] for symbol [s] to [ppf]. *)
let sym_rule : sym -> rule pp = fun s ppf r ->
  incr nb_rules; let sr = s, r in rule ppf (lhs sr, rhs sr)

(** [sign ppf s] outputs the signature [s] to [ppf]. *)
let sign : Sign.t pp = fun ppf sign ->
  (* Get all the dependencies (every needed symbols and rewriting rules). *)
  let deps = Sign.dependencies sign in
  (* Function to iterate over every symbols. *)
  let _iter_symbols : (sym -> unit) -> unit = fun fn ->
    let notin_ghosts _ s = if not (Unif_rule.mem s) then fn s in
    let iter_symbols sign =
      StrMap.iter notin_ghosts Timed.(!(sign.Sign.sign_symbols))
    in
    List.iter (fun (_, sign) -> iter_symbols sign) deps
  in
  (* Print the symbol declarations. *)
  (*let symbol s = add_sym s; out ppf "(FUN %a : t)\n" sym s in
    iter_symbols symbol;*)
  (* Print the rewriting rules. *)
  let rules : sym pp = fun ppf s ->
    match Timed.(!(s.sym_def)) with
    | Some d -> rule ppf (mk_Symb s, d)
    | None -> List.iter (sym_rule s ppf) Timed.(!(s.sym_rules))
  in
  (*iter_symbols rules*)
  let rules : (_ * Sign.t) pp = fun ppf (_, sign) ->
    if sign != Unif_rule.sign then
      let rules _ s = rules ppf s in
      StrMap.iter rules Timed.(!(sign.sign_symbols))
  in
  let pp_sym_name : string SymMap.t pp = fun ppf sym_name ->
    let decl : string pp = fun ppf n -> out ppf "\n%s : t" n in
    let sym _ n = decl ppf n in SymMap.iter sym sym_name
  in
  let pp_pvars : int StrMap.t pp = fun ppf pvars ->
    let typ : int pp = fun ppf k ->
      for _i=1 to k do string ppf "t -> " done; out ppf "t" in
    let decl n k = out ppf "\n%s : %a" n typ k in
    StrMap.iter decl pvars in
  let pp_bvars : IntSet.t pp = fun ppf bvars ->
    let decl : int pp = fun ppf n -> out ppf "\n%d : t" n in
    IntSet.iter (decl ppf) bvars
  in
  let b = Buffer.create 1000 in
  let ppf_rules = Format.formatter_of_buffer b in
  List.iter (rules ppf_rules) deps;
  (* Print the prelude. *)
  out ppf "\
(FUN
lam  : t -> (t -> t) -> t
app  : t -> t -> t
pi   : t -> (t -> t) -> t%a
)
(VAR
$x : t
$y : t -> t
$z : t%a%a
)
(RULES
app (lam $x $y) $z -> $y $z%s
)\n" pp_sym_name !sym_name pp_pvars !pvars pp_bvars !bvars (Buffer.contents b)
