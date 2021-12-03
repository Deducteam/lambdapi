(** Pretty-printing the parser-level AST.

    This module defines functions that allow printing elements of syntax found
    in the parser-level abstract syntax. This is used, for example, to print a
    file in the Lambdapi syntax, given the AST obtained when parsing a file in
    the legacy (Dedukti) syntax. *)

open! Lplib
open Base
open Common
open Pos
open Syntax
open Format
open Core

(** Keywords table. *)
let keyword_table = Hashtbl.create 59

let is_keyword : string -> bool = Hashtbl.mem keyword_table

let _ = let open LpLexer in
  List.iter (fun (s, k) -> Hashtbl.add keyword_table s k)
    [ "abort", ABORT
    ; "admit", ADMIT
    ; "admitted", ADMITTED
    ; "apply", APPLY
    ; "as", AS
    ; "assert", ASSERT
    ; "assertnot", ASSERTNOT
    ; "associative", ASSOCIATIVE
    ; "assume", ASSUME
    ; "begin", BEGIN
    ; "builtin", BUILTIN
    ; "commutative", COMMUTATIVE
    ; "compute", COMPUTE
    ; "constant", CONSTANT
    ; "debug", DEBUG
    ; "end", END
    ; "fail", FAIL
    ; "flag", FLAG
    ; "focus", FOCUS
    ; "generalize", GENERALIZE
    ; "have", HAVE
    ; "in", IN
    ; "induction", INDUCTION
    ; "inductive", INDUCTIVE
    ; "infix", INFIX
    ; "injective", INJECTIVE
    ; "left", ASSOC(Pratter.Left)
    ; "let", LET
    ; "off", SWITCH(false)
    ; "on", SWITCH(true)
    ; "opaque", OPAQUE
    ; "open", OPEN
    ; "prefix", PREFIX
    ; "print", PRINT
    ; "private", PRIVATE
    ; "proofterm", PROOFTERM
    ; "protected", PROTECTED
    ; "prover", PROVER
    ; "prover_timeout", PROVER_TIMEOUT
    ; "quantifier", QUANTIFIER
    ; "refine", REFINE
    ; "reflexivity", REFLEXIVITY
    ; "require", REQUIRE
    ; "rewrite", REWRITE
    ; "right", ASSOC(Pratter.Right)
    ; "rule", RULE
    ; "sequential", SEQUENTIAL
    ; "simplify", SIMPLIFY
    ; "solve", SOLVE
    ; "symbol", SYMBOL
    ; "symmetry", SYMMETRY
    ; "type", TYPE_QUERY
    ; "TYPE", TYPE_TERM
    ; "unif_rule", UNIF_RULE
    ; "verbose", VERBOSE
    ; "why3", WHY3
    ; "with", WITH ]

let raw_ident : string pp = fun ppf s ->
  if is_keyword s then out ppf "{|%a|}" Print.pp_uid s
  else Print.pp_uid ppf s

let ident : p_ident pp = fun ppf {elt;_} -> raw_ident ppf elt

let meta_ident : p_meta_ident pp = fun ppf {elt;_} ->
  match elt with
  | Name s -> raw_ident ppf s
  | Numb i -> out ppf "%d" i

let param_id : p_ident option pp = fun ppf idopt ->
  match idopt with
  | Some(id) -> out ppf "%a" ident id
  | None     -> out ppf "_"

let param_ids : p_ident option list pp = List.pp param_id " "

let raw_path : Path.t pp = List.pp raw_ident "."

let path : p_path pp = fun ppf {elt;_} -> raw_path ppf elt

let qident : p_qident pp = fun ppf {elt=(mp,s);_} ->
  match mp with
  | [] -> raw_ident ppf s
  | _::_ -> out ppf "%a.%a" raw_path mp raw_ident s

(* ends with a space *)
let modifier : p_modifier pp = fun ppf {elt; _} ->
  match elt with
  | P_expo(e)   -> Print.pp_expo ppf e
  | P_mstrat(s) -> Print.pp_match_strat ppf s
  | P_prop(p)   -> Print.pp_prop ppf p
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
    | (P_Iden(qid,false)   , _    ) -> out ppf "%a" qident qid
    | (P_Iden(qid,true )   , _    ) -> out ppf "@@%a" qident qid
    | (P_Wild              , _    ) -> out ppf "_"
    | (P_Meta(mid,ts)      , _    ) -> out ppf "?%a%a" meta_ident mid env ts
    | (P_Patt(idopt,ts)    , _    ) -> out ppf "$%a%a" param_id idopt env ts
    | (P_Appl(t,u)         , `Appl)
    | (P_Appl(t,u)         , `Func) -> out ppf "@[%a@ %a@]" appl t atom u
    | (P_Arro(a,b)         , `Func) -> out ppf "@[%a@ → %a@]" appl a func b
    | (P_Abst(xs,t)        , `Func) ->
        let fn (ids,_,_) = List.for_all ((=) None) ids in
        let ec = !empty_context in
        empty_context := ec && List.for_all fn xs;
        out ppf "@[<2>λ%a,@ %a@]"
          params_list xs
          func t;
        empty_context := ec
    | (P_Prod(xs,b)        , `Func) ->
        out ppf "@[<2>Π%a,@ %a@]" params_list xs func b
    | (P_LLet(x,xs,a,t,u)  , `Func) ->
        out ppf "@[@[<hv2>let @[<2>%a%a%a@] ≔@ %a@ @]in@ %a@]"
          ident x params_list xs typ a func t func u
    | (P_NLit(i)           , _    ) -> out ppf "%i" i
    (* We print minimal parentheses, and ignore the [Wrap] constructor. *)
    | (P_Wrap(t)           , _    ) -> pp priority ppf t
    | (P_Expl(t)           , _    ) -> out ppf "{@[<hv2>%a@]}" func t
    | (_                   , _    ) -> out ppf "(@[<hv2>%a@])" func t
  in
  let rec toplevel ppf t =
    match t.elt with
    | P_Abst(xs,t) -> out ppf "@[<2>λ%a,@ %a@]" params_list xs toplevel t
    | P_Prod(xs,b) -> out ppf "@[<2>Π%a,@ %a@]" params_list xs toplevel b
    | P_Arro(a,b) -> out ppf "@[%a@ → %a@]" appl a toplevel b
    | P_LLet(x,xs,a,t,u) ->
        out ppf "@[@[<hv2>let @[<2>%a%a%a@] ≔@ %a@ @]in@ %a@]"
          ident x params_list xs typ a toplevel t toplevel u
    | _ -> func ppf t
  in
  toplevel ppf t

and params : p_params pp = fun ppf (ids, t, b) ->
  match b with
  | false -> out ppf "@[(@,@[<2>%a%a@]@,)@]" param_ids ids typ t
  | true  -> out ppf "@[{@,@[<2>%a%a@]@,}@]" param_ids ids typ t

(* starts with a space if the list is not empty *)
and params_list : p_params list pp = fun ppf ->
  List.iter (out ppf "@ %a" params)

(* starts with a space if <> None *)
and typ : p_term option pp = fun ppf t ->
  Option.iter (out ppf "@ : %a" term) t

let rule : string -> p_rule pp = fun kw ppf {elt=(l,r);_} ->
  out ppf "%s %a ↪ %a" kw term l term r

let inductive : string -> p_inductive pp =
  let cons ppf (id,a) = out ppf "| %a : %a" ident id term a in
  fun kw ppf {elt=(id,a,cs);_} ->
  out ppf "@[<v>%s %a : %a ≔@,%a@]" kw ident id term a (List.pp cons "@,") cs

let equiv : (p_term * p_term) pp = fun ppf (l,r) ->
  out ppf "%a ≡ %a" term l term r

(** [unpack eqs] transforms a p_term of the form [LpLexer.cons
   (LpLexer.equiv t u) (LpLexer.cons (LpLexer.equiv v w) ...)]  into a
   list [[(t,u); (v,w); ...]]. See unif_rule.ml. *)
let rec unpack : p_term -> (p_term * p_term) list = fun eqs ->
  let is (p,s) id = p = Unif_rule.path && s = id.Term.sym_name in
  match Syntax.p_get_args eqs with
  | ({elt=P_Iden({elt;_},_); _}, [v; w]) ->
      if is elt Unif_rule.cons then
        match Syntax.p_get_args v with
        | ({elt=P_Iden({elt;_},_); _}, [t; u])
             when is elt Unif_rule.equiv -> (t, u) :: unpack w
        | _ -> assert false
      else if is elt Unif_rule.equiv then [(v, w)]
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
  | Rw_Term(t)               -> term ppf t
  | Rw_InTerm(t)             -> out ppf "in %a" term t
  | Rw_InIdInTerm(x,t)       -> out ppf "in %a in %a" ident x term t
  | Rw_IdInTerm(x,t)         -> out ppf "%a in %a" ident x term t
  | Rw_TermInIdInTerm(u,(x,t)) ->
      out ppf "%a in %a in %a" term u ident x term t
  | Rw_TermAsIdInTerm(u,(x,t)) ->
      out ppf "%a as %a in %a" term u ident x term t

let assertion : p_assertion pp = fun ppf a ->
  match a with
  | P_assert_typing (t, a) -> out ppf "@[%a@ : %a@]" term t term a
  | P_assert_conv (t, u)   -> out ppf "@[%a@ ≡ %a@]" term t term u

let query : p_query pp = fun ppf { elt; _ } ->
  match elt with
  | P_query_assert(true, a) -> out ppf "assertnot ⊢ %a" assertion a
  | P_query_assert(false,a) -> out ppf "assert ⊢ %a" assertion a
  | P_query_debug(true ,s) -> out ppf "set debug \"+%s\"" s
  | P_query_debug(false,s) -> out ppf "set debug \"-%s\"" s
  | P_query_flag(s, b) ->
      out ppf "set flag \"%s\" %s" s (if b then "on" else "off")
  | P_query_infer(t, _) -> out ppf "type %a" term t
  | P_query_normalize(t, _) -> out ppf "compute %a" term t
  | P_query_prover s -> out ppf "set prover \"%s\"" s
  | P_query_prover_timeout n -> out ppf "set prover_timeout %d" n
  | P_query_print None -> out ppf "print"
  | P_query_print(Some qid) -> out ppf "print %a" qident qid
  | P_query_proofterm -> out ppf "proofterm"
  | P_query_verbose i -> out ppf "set verbose %i" i

let tactic : p_tactic pp = fun ppf { elt;  _ } ->
  begin match elt with
  | P_tac_admit -> out ppf "admit"
  | P_tac_apply t -> out ppf "apply %a" term t
  | P_tac_assume ids ->
      out ppf "assume%a" (List.pp (pp_unit " " |+ param_id) "") ids
  | P_tac_fail -> out ppf "fail"
  | P_tac_focus i -> out ppf "focus %i" i
  | P_tac_generalize id -> out ppf "generalize %a" ident id
  | P_tac_have (id, t) -> out ppf "have %a: %a" ident id term t
  | P_tac_induction -> out ppf "induction"
  | P_tac_query q -> query ppf q
  | P_tac_refine t -> out ppf "refine %a" term t
  | P_tac_refl -> out ppf "reflexivity"
  | P_tac_rewrite(b,p,t)     ->
      let dir ppf b = if not b then out ppf " left" in
      let pat ppf p = out ppf " [%a]" rw_patt p in
      out ppf "rewrite%a%a %a" dir b (Option.pp pat) p term t
  | P_tac_simpl None -> out ppf "simpl"
  | P_tac_simpl (Some qid) -> out ppf "simpl %a" qident qid
  | P_tac_solve -> out ppf "solve"
  | P_tac_sym -> out ppf "symmetry"
  | P_tac_why3 p ->
      let prover ppf s = out ppf " \"%s\"" s in
      out ppf "why3%a" (Option.pp prover) p
  end;
  out ppf ";"

(* starts with a space if distinct from [Pratter.Neither] *)
let assoc : Pratter.associativity pp = fun ppf a ->
  out ppf (match a with
           | Pratter.Neither -> ""
           | Pratter.Left -> " left"
           | Pratter.Right -> " right")

let notation : Sign.notation pp = fun ppf -> function
  | Infix (a, p) -> out ppf "infix%a %f" assoc a p
  | Prefix p -> out ppf "prefix %f" p
  | Quant -> out ppf "quantifier"
  | _ -> ()

let proof : (p_tactic list * p_proof_end) pp = fun ppf (prf, prf_end) ->
  out ppf "begin@ @[<2>%a@]@ %a"
    (List.pp tactic "@ ") prf
    proof_end prf_end

let command : p_command pp = fun ppf { elt; _ } ->
  begin match elt with
  | P_builtin (s, qid) -> out ppf "@[builtin \"%s\"@ ≔ %a@]" s qident qid
  | P_inductive (_, _, []) -> assert false (* not possible *)
  | P_inductive (ms, xs, i :: il) ->
      out ppf "@[<v>@[%a%a@]%a@,%a@,end@]"
        modifiers ms
        (List.pp params " ") xs
        (inductive "inductive") i
        (List.pp (inductive "with") "@,") il
  | P_notation (qid, n) -> out ppf "notation %a %a" qident qid notation n
  | P_open ps -> out ppf "open %a" (List.pp path " ") ps
  | P_query q -> query ppf q
  | P_require (b, ps) ->
      out ppf "require%a %a"
        (pp_if b (pp_unit " open")) ()
        (List.pp path " ") ps
  | P_require_as (p,i) -> out ppf "@[require %a@ as %a@]" path p ident i
  | P_rules [] -> assert false (* not possible *)
  | P_rules (r :: rs) ->
      out ppf "@[<v>%a@,%a@]" (rule "rule") r (List.pp (rule "with") "@,") rs
  | P_symbol
    { p_sym_mod; p_sym_nam; p_sym_arg; p_sym_typ;
      p_sym_trm; p_sym_prf; p_sym_def } ->
    begin
      out ppf "@[<v>@[<2>%asymbol %a%a%a%a%a@]%a@]"
        modifiers p_sym_mod
        ident p_sym_nam
        params_list p_sym_arg
        typ p_sym_typ
        (pp_if p_sym_def (pp_unit "@ ≔")) ()
        (Option.pp (pp_sep " " |+ term)) p_sym_trm
        (Option.pp (pp_unit "@," |+ proof)) p_sym_prf
    end
  | P_unif_rule ur -> out ppf "unif_rule %a" unif_rule ur
  end;
  out ppf ";"

let ast : ast pp = fun ppf ->
  Stream.iter ((command +| pp_unit "@.") ppf)

(** [beautify cmds] pretty-prints the commands [cmds] to standard output. *)
let beautify : ast -> unit = ast std_formatter
