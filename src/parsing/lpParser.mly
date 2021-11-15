(* Lambdapi Menhir parser. We need to parse UTF8 - and hence use Sedlex.
   Using Sedlex (and not Ocamllex) requires to use the "revised" API of
   Menhir which abstracts the Lexing buffer. *)
%{
  open Lplib
  open Common
  open Pos
  open Syntax
  open Core

  let qid_of_path loc p =
    let (mp, id) = List.split_last p in make_pos loc (mp, id)

  let make_abst startpos ps t endpos =
    if ps = [] then t else make_pos (startpos,endpos) (P_Abst(ps,t))

  let make_prod startpos ps t endpos =
    if ps = [] then t else make_pos (startpos,endpos) (P_Prod(ps,t))
%}

// end of file

%token EOF

// keywords in alphabetical order

%token ABORT
%token ADMIT
%token ADMITTED
%token APPLY
%token AS
%token ASSERT
%token ASSERTNOT
%token ASSOCIATIVE
%token ASSUME
%token BEGIN
%token BUILTIN
%token COMMUTATIVE
%token COMPUTE
%token CONSTANT
%token DEBUG
%token END
%token FAIL
%token FLAG
%token FOCUS
%token GENERALIZE
%token HAVE
%token IN
%token INDUCTION
%token INDUCTIVE
%token INFIX
%token INJECTIVE
%token LET
%token NOTATION
%token OPAQUE
%token OPEN
%token PREFIX
%token PRINT
%token PRIVATE
%token PROOFTERM
%token PROTECTED
%token PROVER
%token PROVER_TIMEOUT
%token QUANTIFIER
%token REFINE
%token REFLEXIVITY
%token REQUIRE
%token REWRITE
%token RULE
%token SEQUENTIAL
%token SIMPLIFY
%token SOLVE
%token SYMBOL
%token SYMMETRY
%token TYPE_QUERY
%token TYPE_TERM
%token UNIF_RULE
%token VERBOSE
%token WHY3
%token WITH

// other tokens

%token <Pratter.associativity> ASSOC
%token <bool * string> DEBUG_FLAGS
%token <int> INT
%token <float> FLOAT
%token <string> STRINGLIT
%token <bool> SWITCH

// symbols

%token ARROW
%token ASSIGN
%token BACKQUOTE
%token COMMA
%token COLON
%token DOT
%token EQUIV
%token HOOK_ARROW
%token LAMBDA
%token L_CU_BRACKET
%token L_PAREN
%token L_SQ_BRACKET
%token PI
%token R_CU_BRACKET
%token R_PAREN
%token R_SQ_BRACKET
%token SEMICOLON
%token TURNSTILE
%token VBAR
%token WILD

// identifiers

%token <string> UID
%token <Syntax.meta_ident> UID_META
%token <string> UID_PAT
%token <Path.t> QID
%token <Path.t> ID_EXPL

// types

%start <Syntax.p_command> command
%start <Syntax.p_qident> id

%type <Sign.notation> notation

%%

sep_ne_list_with_opt_end_sep(arg, sep):
  | a=arg { [a] }
  | a=arg; sep { [a] }
  | a=arg; sep; l=sep_ne_list_with_opt_end_sep(arg, sep) { a :: l }

sep_list_with_opt_end_sep(arg, sep):
  l=loption(sep_ne_list_with_opt_end_sep(arg, sep)) { l }

uid: i=UID { make_pos $sloc i}

id:
  | p=QID { qid_of_path $sloc p}
  | i=UID { make_pos $sloc ([], i) }

path: i=QID { make_pos $sloc i}

term_id:
  | i=id { make_pos $sloc (P_Iden(i, false)) }
  | p=ID_EXPL { make_pos $sloc (P_Iden(qid_of_path $sloc p, true)) }

patt_id: p=UID_PAT { if p = "_" then None else Some(make_pos $sloc p) }

param_id:
  | i=uid { Some i }
  | WILD { None }

params:
  | x=param_id { ([x], None, false) }
  | L_PAREN xs=param_id+ COLON a=term R_PAREN { (xs, Some(a), false) }
  | L_SQ_BRACKET xs=param_id+ a=preceded(COLON, term)? R_SQ_BRACKET
    { (xs, a, true) }

rw_patt:
  | t=term { make_pos $sloc (Rw_Term(t)) }
  | IN t=term { make_pos $sloc (Rw_InTerm(t)) }
  | IN x=uid IN t=term { make_pos $sloc (Rw_InIdInTerm(x, t)) }
  | u=term IN x=term t=preceded(IN, term)?
    { let ident_of_term {elt; _} =
        match elt with
        | P_Iden({elt=([], x); pos}, _) -> Pos.make pos x
        | _ -> $syntaxerror
      in
      match t with
      | Some(t) -> make_pos $sloc (Rw_TermInIdInTerm(u, (ident_of_term x, t)))
      | None -> make_pos $sloc (Rw_IdInTerm(ident_of_term u, x))
    }
  | u=term AS x=uid IN t=term { make_pos $sloc (Rw_TermAsIdInTerm(u,(x,t))) }

tactic:
  | q=query { make_pos $sloc (P_tac_query q) }
  | ADMIT { make_pos $sloc P_tac_admit }
  | APPLY t=term { make_pos $sloc (P_tac_apply t) }
  | ASSUME xs=param_id+ { make_pos $sloc (P_tac_assume xs) }
  | FAIL { make_pos $sloc P_tac_fail }
  | FOCUS i=INT { make_pos $sloc (P_tac_focus i) }
  | GENERALIZE i=uid { make_pos $sloc (P_tac_generalize i) }
  | HAVE i=uid COLON t=term { make_pos $sloc (P_tac_have(i,t)) }
  | INDUCTION { make_pos $sloc P_tac_induction }
  | REFINE t=term { make_pos $sloc (P_tac_refine t) }
  | REFLEXIVITY { make_pos $sloc P_tac_refl }
  | REWRITE d=ASSOC? p=delimited(L_CU_BRACKET, rw_patt, R_CU_BRACKET)? t=term
    { let b = match d with Some Pratter.Left -> false | _ -> true in
      make_pos $sloc (P_tac_rewrite(b,p,t)) }
  | SIMPLIFY i=id? { make_pos $sloc (P_tac_simpl i) }
  | SOLVE { make_pos $sloc P_tac_solve }
  | SYMMETRY { make_pos $sloc P_tac_sym }
  | WHY3 s=STRINGLIT? { make_pos $sloc (P_tac_why3 s) }

modifier:
  | d=ASSOC? ASSOCIATIVE
    { let b = match d with Some Pratter.Left -> true | _ -> false in
      make_pos $sloc (P_prop (Term.Assoc b)) }
  | COMMUTATIVE { make_pos $sloc (P_prop Term.Commu) }
  | CONSTANT { make_pos $sloc (P_prop Term.Const) }
  | INJECTIVE { make_pos $sloc (P_prop Term.Injec) }
  | OPAQUE { make_pos $sloc P_opaq }
  | PRIVATE { make_pos $sloc (P_expo Term.Privat) }
  | PROTECTED { make_pos $sloc (P_expo Term.Protec) }
  | SEQUENTIAL { make_pos $sloc (P_mstrat Term.Sequen) }

float_or_int:
  | p=FLOAT { p }
  | n=INT   { float_of_int n }

notation:
  | INFIX a=ASSOC? p=float_or_int { Infix(Option.get Pratter.Neither a, p) }
  | PREFIX p=float_or_int { Prefix(p) }
  | QUANTIFIER { Quant }

assert_kw:
  | ASSERT { false }
  | ASSERTNOT { true }

query:
  | k=assert_kw ps=params* TURNSTILE t=term COLON a=term
    { let t = make_abst $startpos(ps) ps t $endpos(t) in
      let a = make_prod $startpos(ps) ps a $endpos(a) in
      make_pos $sloc (P_query_assert(k, P_assert_typing(t, a))) }
  | k=assert_kw ps=params* TURNSTILE t=term EQUIV u=term
    { let t = make_abst $startpos(ps) ps t $endpos(t) in
      let u = make_abst $startpos(ps) ps u $endpos(u) in
      make_pos $sloc (P_query_assert(k, P_assert_conv(t, u))) }
  | COMPUTE t=term
    { make_pos $sloc (P_query_normalize(t, {strategy=SNF; steps=None})) }
  | PRINT i=id? { make_pos $sloc (P_query_print i) }
  | PROOFTERM { make_pos $sloc P_query_proofterm }
  | DEBUG fl=DEBUG_FLAGS
    { let (b, s) = fl in make_pos $sloc (P_query_debug(b, s)) }
  | FLAG s=STRINGLIT b=SWITCH { make_pos $sloc (P_query_flag(s,b)) }
  | PROVER s=STRINGLIT { make_pos $sloc (P_query_prover(s)) }
  | PROVER_TIMEOUT i=INT { make_pos $sloc (P_query_prover_timeout(i)) }
  | VERBOSE i=INT { make_pos $sloc (P_query_verbose(i)) }
  | TYPE_QUERY t=term
    { make_pos $sloc (P_query_infer(t, {strategy=NONE; steps=None}))}

proof_end:
  | ABORT { make_pos $sloc Syntax.P_proof_abort }
  | ADMITTED { make_pos $sloc Syntax.P_proof_admitted }
  | END { make_pos $sloc Syntax.P_proof_end }

proof:
  | BEGIN l=subproof+ pe=proof_end { l, pe }
  | BEGIN l=sep_list_with_opt_end_sep(proof_step, SEMICOLON) pe=proof_end
      { [l], pe }

subproof:
  | L_CU_BRACKET l=sep_list_with_opt_end_sep(proof_step, SEMICOLON)
    R_CU_BRACKET { l }

proof_step: t=tactic l=subproof* { Tactic(t, l) }

constructor:
  | i=uid ps=params* COLON t=term
    { (i, make_prod $startpos(ps) ps t $endpos(t)) }

inductive:
  | i=uid ps=params* COLON t=term ASSIGN
    VBAR? l=separated_list(VBAR, constructor)
    { let t = make_prod $startpos(ps) ps t $endpos(t) in
      make_pos $sloc (i,t,l) }

term_proof:
  | t=term { Some t, None }
  | p=proof { None, Some p }
  | t=term p=proof { Some t, Some p }

command:
  | REQUIRE OPEN l=list(path) SEMICOLON
    { make_pos $sloc (P_require(true,l)) }
  | REQUIRE l=list(path) SEMICOLON
    { make_pos $sloc (P_require(false,l)) }
  | REQUIRE i=path AS a=uid SEMICOLON
    { make_pos $sloc (P_require_as(i,a)) }
  | OPEN l=list(path) SEMICOLON
    { make_pos $sloc (P_open l) }
  | ms=modifier* SYMBOL s=uid al=params* COLON a=term
    po=proof? SEMICOLON
    { let sym =
        {p_sym_mod=ms; p_sym_nam=s; p_sym_arg=al; p_sym_typ=Some(a);
         p_sym_trm=None; p_sym_def=false; p_sym_prf= po}
      in make_pos $sloc (P_symbol(sym)) }
  | ms=modifier* SYMBOL s=uid al=params* ao=preceded(COLON, term)?
    ASSIGN tp=term_proof SEMICOLON
    { let sym =
        {p_sym_mod=ms; p_sym_nam=s; p_sym_arg=al; p_sym_typ=ao;
         p_sym_trm=fst tp; p_sym_prf= snd tp; p_sym_def=true}
      in make_pos $sloc (P_symbol(sym)) }
  | ms=modifier* xs=params* INDUCTIVE
    is=separated_nonempty_list(WITH, inductive) SEMICOLON
      { make_pos $sloc (P_inductive(ms,xs,is)) }
  | RULE rs=separated_nonempty_list(WITH, rule) SEMICOLON
      { make_pos $sloc (P_rules(rs)) }
  | BUILTIN s=STRINGLIT ASSIGN i=id SEMICOLON
    { make_pos $loc (P_builtin(s,i)) }
  | UNIF_RULE r=unif_rule SEMICOLON { make_pos $loc (P_unif_rule(r)) }
  | NOTATION i=id n=notation SEMICOLON { make_pos $loc (P_notation(i,n)) }
  | q=query SEMICOLON { make_pos $sloc (P_query(q)) }
  | EOF { raise End_of_file }

env: DOT L_SQ_BRACKET ts=separated_list(SEMICOLON, term) R_SQ_BRACKET
  { ts }

aterm:
  | ti=term_id { ti }
  | WILD { make_pos $sloc P_Wild }
  | TYPE_TERM { make_pos $sloc P_Type }
  | m=UID_META e=env?
      { let mid = make_pos $loc(m) m in
        make_pos $sloc (P_Meta(mid, Option.map Array.of_list e)) }
  | p=patt_id e=env? { make_pos $sloc (P_Patt(p,Option.map Array.of_list e)) }
  | L_PAREN t=term R_PAREN { make_pos $sloc (P_Wrap(t)) }
  | L_SQ_BRACKET t=term R_SQ_BRACKET { make_pos $sloc (P_Expl(t)) }
  | n=INT { make_pos $sloc (P_NLit(n)) }

saterm:
  | t=saterm u=aterm { make_pos $sloc (P_Appl(t,u)) }
  | t=aterm { t }

bterm:
  | BACKQUOTE q=term_id b=binder
    { let b = make_pos $loc(b) (P_Abst(fst b, snd b)) in
      make_pos $sloc (P_Appl(q, b)) }
  | PI b=binder { make_pos $sloc (P_Prod(fst b, snd b)) }
  | LAMBDA b=binder { make_pos $sloc (P_Abst(fst b, snd b)) }
  | LET x=uid a=params* b=preceded(COLON, term)? ASSIGN t=term IN u=term
      { make_pos $sloc (P_LLet(x, a, b, t, u)) }

term:
  | t=bterm { t }
  | t=saterm { t }
  | t=saterm u=bterm { make_pos $sloc (P_Appl(t,u)) }
  | t=saterm ARROW u=term { make_pos $sloc (P_Arro(t, u)) }

binder:
  | ps=params+ COMMA t=term { (ps, t) }
  | p=param_id COLON a=term COMMA t=term { ([[p], Some a, false], t) }

rule: l=term HOOK_ARROW r=term { make_pos $sloc (l, r) }

equation: l=term EQUIV r=term { (l, r) }

unif_rule: e=equation HOOK_ARROW
  L_CU_BRACKET es=separated_nonempty_list(SEMICOLON, equation) R_CU_BRACKET
    { (* FIXME: give sensible positions instead of Pos.none and P.appl. *)
      let equiv = P.qiden Unif_rule.path Unif_rule.equiv.sym_name in
      let cons = P.qiden Unif_rule.path Unif_rule.cons.sym_name in
      let mk_equiv (t, u) = P.appl (P.appl equiv t) u in
      let lhs = mk_equiv e in
      let es = List.rev_map mk_equiv es in
      let (en, es) = List.(hd es, tl es) in
      let cat e es = P.appl (P.appl cons e) es in
      let rhs = List.fold_right cat es en in
      make_pos $sloc (lhs, rhs) }

%%
