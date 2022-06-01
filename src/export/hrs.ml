(** This module provides a function to translate a signature to the HRS format
   used in the confluence competition.

    @see <http://project-coco.uibk.ac.at/problems/hrs.php>.

- Function symbol names are prefixed by ["c_"], bound variables by ["v_"], and
   pattern variables by ["$"] because, in the hrs format, variable names must
   be distinct from function symbol names.

- Function symbol names are fully qualified but ["."] is replaced by ["_"]
   because ["."] cannot be used in identifiers (["."]  is used in lambda
   abstractions).

- Lambdapi terms are translated to the following HRS term algebra with a
   unique type "term":

  lam : term -> (term -> term) -> term

  app : term -> term -> term

  pi : term -> (term -> term) -> term

TO FIX:

- Have only one VAR section, one FUN section and one RULES section. Solution:
   use 3 buffers: one for symbols, one for variables and one for rules.

- Pattern variable names are not valid anymore: they should be prefixed by the
   rule number.

- Translate let by beta-redex or new symbol.

- Optim: do not generate the list of dependencies but iterate over them.

*)

open Lplib open Base open Extra
open Timed
open Core open Term open Print

(** [sym ppf s] outputs the symbol [s] to [ppf]. *)
let sym : sym pp = fun ppf s ->
  out ppf "%a_%s" (List.pp string "_") s.sym_path s.sym_name

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
  | Vari x -> out ppf "%a" var x
  | Symb s -> sym ppf s
  | Patt(_,n,[||]) -> out ppf "$%s" n
  | Patt(i,n,ts) ->
    term ppf
      (Array.fold_left (fun t u -> mk_Appl(t,u)) (mk_Patt(i,n,[||])) ts)
  | Appl(t,u) -> out ppf "app(%a,%a)" term t term u
  | Abst(a,b) ->
    let x, b = Bindlib.unbind b in
    out ppf "lam(%a,\\%a.%a)" term a var x term b
  | Prod(a,b)    ->
    let x, b = Bindlib.unbind b in
    out ppf "pi(%a,\\%a.%a)" term a var x term b
  | LLet(_,t,u) -> term ppf (Bindlib.subst u t)  (*FIXME*)

(** [rule ppf (l,r)] outputs the rule [l --> r] to [ppf]. *)
let rule : (term * term) pp = fun ppf (lhs, rhs) ->
  (* gets pattern and binded variable names *)
  let add_var_names : StrSet.t -> term -> StrSet.t = fun ns t ->
    let names = Stdlib.ref ns in
    let fn t =
      match t with
      | Patt(_,n,_) -> Stdlib.(names := StrSet.add ("$" ^ n) !names)
      | Abst(_,b) ->
        let (x, _) = Bindlib.unbind b in
        Stdlib.(names := StrSet.add (Bindlib.name_of x) !names)
      | _           -> ()
    in
    LibTerm.iter fn t;
    Stdlib.(!names)
  in
  let names = add_var_names StrSet.empty lhs in
  let names = add_var_names names rhs in
  if not (StrSet.is_empty names) then
    begin
      let name ppf x = out ppf "  %s : term\n" x in
      let strset ppf = StrSet.iter (name ppf) in
      out ppf "(VAR\n%a)\n" strset names
    end;
  (* Print the rewriting rule. *)
  out ppf "(RULES %a" term lhs;
  out ppf "\n    -> %a)\n" term rhs

(** [sym_rule ppf s r] outputs the rule declaration corresponding [r]
   (on the symbol [s]), to [ppf]. *)
let sym_rule : sym -> rule pp = fun s ppf r ->
  let sr = s, r in rule ppf (lhs sr, rhs sr)

(** [sign ppf s] outputs the signature [s] to [ppf]. *)
let sign : Sign.t pp = fun ppf sign ->
  (* Get all the dependencies (every needed symbols and rewriting rules). *)
  let deps = Sign.dependencies sign in
  (* Function to iterate over every symbols. *)
  let iter_symbols : (sym -> unit) -> unit = fun fn ->
    let notin_ghosts _ s = if not (Unif_rule.mem s) then fn s in
    let iter_symbols sign =
      StrMap.iter notin_ghosts Sign.(!(sign.sign_symbols))
    in
    List.iter (fun (_, sign) -> iter_symbols sign) deps
  in
  (* Print the prelude. *)
  out ppf "\
(FUN
  lam  : term -> (term -> term) -> term
  app  : term -> term -> term
  pi   : term -> (term -> term) -> term
  TYPE : term
)

(COMMENT beta-reduction)
(VAR
  m_typ : term
  m_B   : term
  m_F   : term -> term
)
(RULES app (lam m_typ m_F) m_B -> m_F m_B)
";
  (* Print the symbol declarations. *)
  out ppf "\n(COMMENT symbols)\n";
  let symbol s = out ppf "(FUN %a : term)\n" sym s in
  iter_symbols symbol;
  (* Print the rewriting rules. *)
  out ppf "\n(COMMENT rewriting rules)\n";
  let rules s =
    match !(s.sym_def) with
    | Some d -> rule ppf (mk_Symb s, d)
    | None -> List.iter (sym_rule s ppf) !(s.sym_rules)
  in
  iter_symbols rules
