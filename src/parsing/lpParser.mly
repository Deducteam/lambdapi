(** Lambdapi parser, using the parser generator Menhir. *)

%{
  open Lplib
  open Common
  open Pos
  open Syntax
  open Core

  let qid_of_path lps = function
    | [] -> assert false
    | id::mp -> make_pos lps (List.rev mp, id)

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
%token <bool> ASSERT
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

%token <bool * string> DEBUG_FLAGS
%token <int> INT
%token <float> FLOAT
%token <Pratter.associativity> SIDE
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
%token UNDERSCORE
%token VBAR

// identifiers

%token <string> UID
%token <string> UID_EXPL
%token <Syntax.meta_ident> UID_META
%token <string> UID_PATT
%token <Path.t> QID
%token <Path.t> QID_EXPL

// types

%start <Syntax.p_command> command
%start <Syntax.p_qident> qid

%%

command:
  | REQUIRE OPEN l=list(path) SEMICOLON
    { make_pos $sloc (P_require(true,l)) }
  | REQUIRE l=list(path) SEMICOLON
    { make_pos $sloc (P_require(false,l)) }
  | REQUIRE p=path AS i=uid SEMICOLON
    { make_pos $sloc (P_require_as(p,i)) }
  | OPEN l=list(path) SEMICOLON
    { make_pos $sloc (P_open l) }
  | ms=modifier* SYMBOL s=uid al=param_list* COLON a=term po=proof? SEMICOLON
    { let sym =
        {p_sym_mod=ms; p_sym_nam=s; p_sym_arg=al; p_sym_typ=Some(a);
         p_sym_trm=None; p_sym_def=false; p_sym_prf=po}
      in make_pos $sloc (P_symbol(sym)) }
  | ms=modifier* SYMBOL s=uid al=param_list* ao=preceded(COLON, term)?
    ASSIGN tp=term_proof SEMICOLON
    { let sym =
        {p_sym_mod=ms; p_sym_nam=s; p_sym_arg=al; p_sym_typ=ao;
         p_sym_trm=fst tp; p_sym_prf=snd tp; p_sym_def=true}
      in make_pos $sloc (P_symbol(sym)) }
  | ms=modifier* xs=param_list* INDUCTIVE
    is=separated_nonempty_list(WITH, inductive) SEMICOLON
      { make_pos $sloc (P_inductive(ms,xs,is)) }
  | RULE rs=separated_nonempty_list(WITH, rule) SEMICOLON
      { make_pos $sloc (P_rules(rs)) }
  | BUILTIN s=STRINGLIT ASSIGN i=qid SEMICOLON
    { make_pos $loc (P_builtin(s,i)) }
  | UNIF_RULE r=unif_rule SEMICOLON { make_pos $loc (P_unif_rule(r)) }
  | NOTATION i=qid n=notation SEMICOLON { make_pos $loc (P_notation(i,n)) }
  | q=query SEMICOLON { make_pos $sloc (P_query(q)) }
  | EOF { raise End_of_file }

query:
  | k=ASSERT ps=param_list* TURNSTILE t=term COLON a=term
    { let t = make_abst $startpos(ps) ps t $endpos(t) in
      let a = make_prod $startpos(ps) ps a $endpos(a) in
      make_pos $sloc (P_query_assert(k, P_assert_typing(t, a))) }
  | k=ASSERT ps=param_list* TURNSTILE t=term EQUIV u=term
    { let t = make_abst $startpos(ps) ps t $endpos(t) in
      let u = make_abst $startpos(ps) ps u $endpos(u) in
      make_pos $sloc (P_query_assert(k, P_assert_conv(t, u))) }
  | COMPUTE t=term
    { make_pos $sloc (P_query_normalize(t, {strategy=SNF; steps=None})) }
  | PRINT i=qid? { make_pos $sloc (P_query_print i) }
  | PROOFTERM { make_pos $sloc P_query_proofterm }
  | DEBUG fl=DEBUG_FLAGS
    { let (b, s) = fl in make_pos $sloc (P_query_debug(b, s)) }
  | FLAG s=STRINGLIT b=SWITCH { make_pos $sloc (P_query_flag(s,b)) }
  | PROVER s=STRINGLIT { make_pos $sloc (P_query_prover(s)) }
  | PROVER_TIMEOUT i=INT { make_pos $sloc (P_query_prover_timeout(i)) }
  | VERBOSE i=INT { make_pos $sloc (P_query_verbose(i)) }
  | TYPE_QUERY t=term
    { make_pos $sloc (P_query_infer(t, {strategy=NONE; steps=None}))}

path:
  | UID { raise Error.NotQualified }
  | p=QID { make_pos $sloc (List.rev p) }

modifier:
  | d=SIDE? ASSOCIATIVE
    { let b = match d with Some Pratter.Left -> true | _ -> false in
      make_pos $sloc (P_prop (Term.Assoc b)) }
  | COMMUTATIVE { make_pos $sloc (P_prop Term.Commu) }
  | CONSTANT { make_pos $sloc (P_prop Term.Const) }
  | INJECTIVE { make_pos $sloc (P_prop Term.Injec) }
  | OPAQUE { make_pos $sloc P_opaq }
  | PRIVATE { make_pos $sloc (P_expo Term.Privat) }
  | PROTECTED { make_pos $sloc (P_expo Term.Protec) }
  | SEQUENTIAL { make_pos $sloc (P_mstrat Term.Sequen) }

uid: s=UID { make_pos $sloc s}

param_list:
  | x=param { ([x], None, false) }
  | L_PAREN xs=param+ COLON a=term R_PAREN { (xs, Some(a), false) }
  | L_SQ_BRACKET xs=param+ a=preceded(COLON, term)? R_SQ_BRACKET
    { (xs, a, true) }

param:
  | s=uid { Some s }
  | UNDERSCORE { None }

term:
  | t=bterm { t }
  | t=saterm { t }
  | t=saterm u=bterm { make_pos $sloc (P_Appl(t,u)) }
  | t=saterm ARROW u=term { make_pos $sloc (P_Arro(t, u)) }

bterm:
  | BACKQUOTE q=term_id b=binder
    { let b = make_pos $loc(b) (P_Abst(fst b, snd b)) in
      make_pos $sloc (P_Appl(q, b)) }
  | PI b=binder { make_pos $sloc (P_Prod(fst b, snd b)) }
  | LAMBDA b=binder { make_pos $sloc (P_Abst(fst b, snd b)) }
  | LET x=uid a=param_list* b=preceded(COLON, term)? ASSIGN t=term IN u=term
      { make_pos $sloc (P_LLet(x, a, b, t, u)) }

saterm:
  | t=saterm u=aterm { make_pos $sloc (P_Appl(t,u)) }
  | t=aterm { t }

aterm:
  | ti=term_id { ti }
  | UNDERSCORE { make_pos $sloc P_Wild }
  | TYPE_TERM { make_pos $sloc P_Type }
  | s=UID_META e=env?
    { let i = make_pos $loc(s) s in
      make_pos $sloc (P_Meta(i, Option.map Array.of_list e)) }
  | s=UID_PATT e=env?
    { let i = if s = "_" then None else Some(make_pos $loc(s) s) in
      make_pos $sloc (P_Patt(i, Option.map Array.of_list e)) }
  | L_PAREN t=term R_PAREN { make_pos $sloc (P_Wrap(t)) }
  | L_SQ_BRACKET t=term R_SQ_BRACKET { make_pos $sloc (P_Expl(t)) }
  | n=INT { make_pos $sloc (P_NLit(n)) }

env: DOT L_SQ_BRACKET ts=separated_list(SEMICOLON, term) R_SQ_BRACKET { ts }

term_id:
  | i=qid { make_pos $sloc (P_Iden(i, false)) }
  | i=qid_expl { make_pos $sloc (P_Iden(i, true)) }

qid:
  | s=UID { make_pos $sloc ([], s) }
  | p=QID { qid_of_path $sloc p }

qid_expl:
  | s=UID_EXPL { make_pos $sloc ([], s) }
  | p=QID_EXPL { qid_of_path $sloc p }

binder:
  | ps=param_list+ COMMA t=term { (ps, t) }
  | p=param COLON a=term COMMA t=term { ([[p], Some a, false], t) }

term_proof:
  | t=term { Some t, None }
  | p=proof { None, Some p }
  | t=term p=proof { Some t, Some p }

proof:
  | BEGIN l=subproof+ pe=proof_end { l, pe }
  | BEGIN l=loption(proof_steps) pe=proof_end { [l], pe }

subproof: L_CU_BRACKET l=loption(proof_steps) R_CU_BRACKET { l }

proof_steps:
  | a=proof_step { [a] }
  | a=proof_step SEMICOLON { [a] }
  | a=proof_step SEMICOLON l=proof_steps { a :: l }

proof_step: t=tactic l=subproof* { Tactic(t, l) }

proof_end:
  | ABORT { make_pos $sloc Syntax.P_proof_abort }
  | ADMITTED { make_pos $sloc Syntax.P_proof_admitted }
  | END { make_pos $sloc Syntax.P_proof_end }

tactic:
  | q=query { make_pos $sloc (P_tac_query q) }
  | ADMIT { make_pos $sloc P_tac_admit }
  | APPLY t=term { make_pos $sloc (P_tac_apply t) }
  | ASSUME xs=param+ { make_pos $sloc (P_tac_assume xs) }
  | FAIL { make_pos $sloc P_tac_fail }
  | GENERALIZE i=uid { make_pos $sloc (P_tac_generalize i) }
  | HAVE i=uid COLON t=term { make_pos $sloc (P_tac_have(i,t)) }
  | INDUCTION { make_pos $sloc P_tac_induction }
  | REFINE t=term { make_pos $sloc (P_tac_refine t) }
  | REFLEXIVITY { make_pos $sloc P_tac_refl }
  | REWRITE d=SIDE? p=rw_patt_spec? t=term
    { let b = match d with Some Pratter.Left -> false | _ -> true in
      make_pos $sloc (P_tac_rewrite(b,p,t)) }
  | SIMPLIFY i=qid? { make_pos $sloc (P_tac_simpl i) }
  | SOLVE { make_pos $sloc P_tac_solve }
  | SYMMETRY { make_pos $sloc P_tac_sym }
  | WHY3 s=STRINGLIT? { make_pos $sloc (P_tac_why3 s) }

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

rw_patt_spec: DOT L_SQ_BRACKET p=rw_patt R_SQ_BRACKET { p }

inductive: i=uid ps=param_list* COLON t=term ASSIGN
    VBAR? l=separated_list(VBAR, constructor)
    { let t = make_prod $startpos(ps) ps t $endpos(t) in
      make_pos $sloc (i,t,l) }

constructor: i=uid ps=param_list* COLON t=term
    { (i, make_prod $startpos(ps) ps t $endpos(t)) }

rule: l=term HOOK_ARROW r=term { make_pos $sloc (l, r) }

unif_rule: e=equation HOOK_ARROW
  L_SQ_BRACKET es=separated_nonempty_list(SEMICOLON, equation) R_SQ_BRACKET
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

equation: l=term EQUIV r=term { (l, r) }

notation:
  | INFIX a=SIDE? p=float_or_int { Infix(Option.get Pratter.Neither a, p) }
  | PREFIX p=float_or_int { Sign.Prefix(p) }
  | QUANTIFIER { Quant }

float_or_int:
  | p=FLOAT { p }
  | n=INT   { float_of_int n }

%%
