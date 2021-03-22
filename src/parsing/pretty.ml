(** Pretty-printing the parser-level AST.

    This module defines functions that allow printing elements of syntax found
    in the parser-level abstract syntax. This is used, for example, to print a
    file in the Lambdapi syntax, given the AST obtained when parsing a file in
    the legacy (Dedukti) syntax. *)

open! Lplib
open Base
open Common
open Error
open Pos
open Syntax
open Format

let out = fprintf

(** check whether identifiers are Lambdapi keywords. *)
let check_keywords = ref false

let raw_ident : popt -> string pp = fun pos ppf s ->
  if !check_keywords && LpLexer.is_keyword s then
    fatal pos "Identifier [%s] is a Lambdapi keyword." s
  else LpLexer.pp_uid ppf s

let ident : p_ident pp = fun ppf {elt=s; pos} -> raw_ident pos ppf s

let meta_ident : p_meta_ident pp = fun ppf {elt; pos} ->
  match elt with
  | Name s -> raw_ident pos ppf s
  | Numb i -> out ppf "%d" i

let param_id : p_ident option pp = fun ppf idopt ->
  match idopt with
  | Some(id) -> out ppf "%a" ident id
  | None     -> out ppf "_"

let param_ids : p_ident option list pp = List.pp param_id " "

let raw_path : popt -> Path.t pp = fun pos -> List.pp (raw_ident pos) "."

let path : p_path pp = fun ppf {elt=p;pos} -> raw_path pos ppf p

let qident : p_qident pp = fun ppf {elt=(mp,s); pos} ->
  match mp with
  | [] -> raw_ident pos ppf s
  | _::_ -> out ppf "%a.%a" (raw_path pos) mp (raw_ident pos) s

(* ends with a space *)
let modifier : p_modifier pp = fun ppf {elt; _} ->
  match elt with
  | P_expo(e)   -> Tags.pp_expo ppf e
  | P_mstrat(s) -> Tags.pp_match_strat ppf s
  | P_prop(p)   -> Tags.pp_prop ppf p
  | P_opaq      -> out ppf "opaque "

(* ends with a space if the list is not empty *)
let modifiers : p_modifier list pp = List.pp modifier ""

(** The possible priority levels are [`Func] (top level, including abstraction
   and product), [`Appl] (application) and [`Atom] (smallest priority). *)
type priority = [`Func | `Appl | `Atom]

let rec term : p_term pp = fun ppf t ->
  let empty_context = ref true in
  let rec atom ppf t = pp `Atom ppf t
  and appl ppf t = pp `Appl ppf t
  and func ppf t = pp `Func ppf t
  and pp priority ppf t =
    let env ppf ts =
      match ts with
      | None -> ()
      | Some [||] when !empty_context -> ()
      | Some ts -> out ppf "[%a]" (Array.pp func "; ") ts
    in
    match (t.elt, priority) with
    | (P_Type              , _    ) -> out ppf "TYPE"
    | (P_Iden(qid,_)       , _    ) -> out ppf "%a" qident qid
    | (P_Wild              , _    ) -> out ppf "_"
    | (P_Meta(mid,ts)      , _    ) -> out ppf "?%a%a" meta_ident mid env ts
    | (P_Patt(None   ,ts)  , _    ) -> out ppf "$_%a" env ts
    | (P_Patt(Some(x),ts)  , _    ) -> out ppf "$%a%a" ident x env ts
    | (P_Appl(t,u)         , `Appl)
    | (P_Appl(t,u)         , `Func) -> out ppf "%a %a" appl t atom u
    | (P_Arro(a,b)         , `Func) -> out ppf "%a → %a" appl a func b
    | (P_Abst(xs,t)        , `Func) ->
        out ppf "λ%a, " params_list xs;
        let fn (ids,_,_) = List.for_all ((=) None) ids in
        let ec = !empty_context in
        empty_context := ec && List.for_all fn xs;
        func ppf t;
        empty_context := ec
    | (P_Prod(xs,b)        , `Func) ->
        out ppf "Π%a, %a" params_list xs func b
    | (P_LLet(x,xs,a,t,u)  , `Func) ->
        out ppf "let %a%a%a ≔ %a in %a"
          ident x params_list xs typ a func t func u
    | (P_NLit(i)           , _    ) -> out ppf "%i" i
    (* We print minimal parentheses, and ignore the [Wrap] constructor. *)
    | (P_Wrap(t)           , _    ) -> pp priority ppf t
    | (P_Expl(t)           , _    ) -> out ppf "{%a}" func t
    | (_                   , _    ) -> out ppf "(%a)" func t
  in
  let rec toplevel ppf t =
    match t.elt with
    | P_Abst(xs,t) -> out ppf "λ%a, %a" params_list xs toplevel t
    | P_Prod(xs,b) -> out ppf "Π%a, %a" params_list xs toplevel b
    | P_Arro(a,b) -> out ppf "%a → %a" appl a toplevel b
    | P_LLet(x,xs,a,t,u) ->
        out ppf "let %a%a%a ≔ %a in %a"
          ident x params_list xs typ a toplevel t toplevel u
    | _ -> func ppf t
  in
  toplevel ppf t

and params : p_params pp = fun ppf (ids,ao,b) ->
  match (ao,b) with
  | (None   , false) -> out ppf "%a" param_ids ids
  | (None   , true ) -> out ppf "{%a}" param_ids ids
  | (Some(a), false) -> out ppf "(%a : %a)" param_ids ids term a
  | (Some(a), true ) -> out ppf "{%a : %a}" param_ids ids term a

(* starts with a space if the list is not empty *)
and params_list : p_params list pp = fun ppf ->
  List.iter (out ppf " %a" params)

(* starts with a space if <> None *)
and typ : p_term option pp = fun ppf t ->
  Option.iter (out ppf " : %a" term) t

let rule : string -> p_rule pp = fun kw ppf {elt=(l,r);_} ->
  out ppf "%s %a ↪ %a" kw term l term r

let inductive : string -> p_inductive pp =
  let cons ppf (id,a) = out ppf "\n| %a : %a" ident id term a in
  fun kw ppf {elt=(id,a,cs);_} ->
  out ppf "%s %a : %a ≔%a" kw ident id term a (List.pp cons "") cs

let equiv : (p_term * p_term) pp = fun ppf (l,r) ->
  out ppf "%a ≡ %a" term l term r

(** [unpack eqs] transforms a p_term of the form [LpLexer.cons
   (LpLexer.equiv t u) (LpLexer.cons (LpLexer.equiv v w) ...)]  into a
   list [[(t,u); (v,w); ...]]. See unif_rule.ml. *)
let rec unpack : p_term -> (p_term * p_term) list = fun eqs ->
  let is (p,s) id = p = LpLexer.unif_rule_path && s = id in
  match Syntax.p_get_args eqs with
  | ({elt=P_Iden({elt;_},_); _}, [v; w]) ->
      if is elt LpLexer.cons then
        match Syntax.p_get_args v with
        | ({elt=P_Iden({elt;_},_); _}, [t; u])
             when is elt LpLexer.equiv -> (t, u) :: unpack w
        | _ -> assert false
      else if is elt LpLexer.equiv then [(v, w)]
      else assert false
  | _ -> assert false

let unif_rule : p_rule pp = fun ppf {elt=(l,r);_} ->
  let lhs =
    match Syntax.p_get_args l with
    | (_, [t; u]) -> (t, u)
    | _           -> assert false
  in
  out ppf "%a ↪ [%a]" equiv lhs (List.pp equiv "; ") (unpack r)

let proof_end : p_proof_end pp = fun ppf pe ->
  out ppf (match pe.elt with
           | P_proof_end   -> "end"
           | P_proof_admitted -> "admitted"
           | P_proof_abort -> "abort")

let rw_patt : p_rw_patt pp = fun ppf p ->
  match p.elt with
  | P_rw_Term(t)               -> term ppf t
  | P_rw_InTerm(t)             -> out ppf "in %a" term t
  | P_rw_InIdInTerm(x,t)       -> out ppf "in %a in %a" ident x term t
  | P_rw_IdInTerm(x,t)         -> out ppf "%a in %a" ident x term t
  | P_rw_TermInIdInTerm(u,x,t) ->
      out ppf "%a in %a in %a" term u ident x term t
  | P_rw_TermAsIdInTerm(u,x,t) ->
      out ppf "%a as %a in %a" term u ident x term t

let assertion : p_assertion pp = fun ppf a ->
  match a with
  | P_assert_typing(t,a) -> out ppf "%a : %a" term t term a
  | P_assert_conv(t,u)   -> out ppf "%a ≡ %a" term t term u

let query : p_query pp = fun ppf q ->
  match q.elt with
  | P_query_assert(true, a) -> out ppf "assertnot %a" assertion a
  | P_query_assert(false,a) -> out ppf "assert %a" assertion a
  | P_query_verbose(i) -> out ppf "set verbose %i" i
  | P_query_debug(true ,s) -> out ppf "set debug \"+%s\"" s
  | P_query_debug(false,s) -> out ppf "set debug \"-%s\"" s
  | P_query_flag(s, b) ->
      out ppf "set flag \"%s\" %s" s (if b then "on" else "off")
  | P_query_infer(t, _) -> out ppf "type %a" term t
  | P_query_normalize(t, _) -> out ppf "compute %a" term t
  | P_query_prover(s) -> out ppf "set prover \"%s\"" s
  | P_query_prover_timeout(n) -> out ppf "set prover_timeout %d" n
  | P_query_print(None) -> out ppf "print"
  | P_query_print(Some qid) -> out ppf "print %a" qident qid
  | P_query_proofterm -> out ppf "proofterm"

let tactic : p_tactic pp = fun ppf t ->
  begin match t.elt with
  | P_tac_refine(t) -> out ppf "refine %a" term t
  | P_tac_assume(xs) ->
      let param_id ppf x = out ppf " %a" param_id x in
      out ppf "assume%a" (List.pp param_id "") xs
  | P_tac_apply(t) -> out ppf "apply %a" term t
  | P_tac_simpl None -> out ppf "simpl"
  | P_tac_simpl (Some qid) -> out ppf "simpl %a" qident qid
  | P_tac_rewrite(b,p,t)     ->
      let dir ppf b = if not b then out ppf " left" in
      let pat ppf p = out ppf " [%a]" rw_patt p in
      out ppf "rewrite%a%a %a" dir b (Option.pp pat) p term t
  | P_tac_refl -> out ppf "reflexivity"
  | P_tac_sym -> out ppf "symmetry"
  | P_tac_focus(i) -> out ppf "focus %i" i
  | P_tac_why3(p) ->
      let prover ppf s = out ppf " \"%s\"" s in
      out ppf "why3%a" (Option.pp prover) p
  | P_tac_query(q) -> query ppf q
  | P_tac_fail -> out ppf "fail"
  | P_tac_solve -> out ppf "solve"
  | P_tac_induction -> out ppf "induction"
  | P_tac_admit -> out ppf "admit"
  end;
  out ppf ";"

(* starts with a space if distinct from [Pratter.Neither] *)
let assoc : Pratter.associativity pp = fun ppf a ->
  out ppf (match a with
           | Pratter.Neither -> ""
           | Pratter.Left -> " left"
           | Pratter.Right -> " right")

let notation : notation pp = fun ppf n ->
  match n with
  | Infix(a,p) -> out ppf "infix%a %f" assoc a p
  | Prefix(p) -> out ppf "prefix %f" p
  | Quant -> out ppf "quantifier"
  | _ -> ()

let command : p_command pp = fun ppf {elt;_} ->
  begin match elt with
  | P_require(b,ps) ->
      let op = if b then " open" else "" in
      out ppf "require%s %a" op (List.pp path " ") ps
  | P_require_as(p,i) -> out ppf "require %a as %a" path p ident i
  | P_open(ps) -> out ppf "open %a" (List.pp path " ") ps
  | P_symbol{p_sym_mod;p_sym_nam;p_sym_arg;p_sym_typ;p_sym_trm;p_sym_prf
             ;p_sym_def} ->
    begin
      out ppf "%asymbol %a%a%a" modifiers p_sym_mod ident p_sym_nam
        params_list p_sym_arg typ p_sym_typ;
      if p_sym_def then out ppf " ≔";
      Option.iter (out ppf " %a" term) p_sym_trm;
      match p_sym_prf with
      | None -> ()
      | Some(ts,pe) ->
          let tactic ppf = out ppf "\n  %a" tactic in
          out ppf "\nbegin%a\n%a" (List.pp tactic "") ts proof_end pe
    end
  | P_rules [] -> assert false (* not possible *)
  | P_rules (r::rs) ->
      out ppf "%a" (rule "rule") r;
      List.iter (out ppf "%a" (rule "\nwith")) rs
  | P_inductive(_, _, []) -> assert false (* not possible *)
  | P_inductive(ms, xs, i::il) ->
      out ppf "%a%a%a%a\nend"
        modifiers ms
        (List.pp params " ") xs
        (inductive "inductive") i
        (List.pp (inductive "\nwith") "") il
  | P_builtin(s,qid) -> out ppf "builtin \"%s\" ≔ %a" s qident qid
  | P_notation(qid,n) -> out ppf "notation %a %a" qident qid notation n
  | P_unif_rule(ur) -> out ppf "unif_rule %a" unif_rule ur
  | P_query(q) -> query ppf q
  end;
  out ppf ";"

let ast : ast pp = fun ppf ->
  Stream.iter (fun c -> command ppf c; pp_print_newline ppf ())

(** [beautify cmds] pretty-prints the commands [cmds] to standard output. *)
let beautify : ast -> unit = ast std_formatter
