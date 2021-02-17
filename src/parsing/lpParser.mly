(* Lambdapi Menhir parser. We need to parse UTF8 - and hence use Sedlex.
   Using Sedlex (and not Ocamllex) requires to use the "revised" API of
   Menhir which abstracts the Lexing buffer. *)
%{
    open Lplib
    open Common
    open Pos
    open Syntax

    let make_pos : Lexing.position * Lexing.position -> 'a -> 'a loc =
      fun lps elt -> Pos.in_pos (locate lps) elt

    let qid_of_path loc p =
      let (mp, id) = List.split_last p in make_pos loc (mp, id)
 %}

// end of file

%token EOF

// keywords in alphabetical order

%token ABORT
%token ADMIT
%token APPLY
%token AS
%token ASSERT
%token ASSERT_NOT
%token ASSUME
%token BEGIN
%token BUILTIN
%token COMPUTE
%token CONSTANT
%token DEBUG
%token END
%token FAIL
%token FLAG
%token FOCUS
%token IN
%token INDUCTION
%token INDUCTIVE
%token INFIX
%token INJECTIVE
%token LET
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
%token SET
%token SIMPL
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

%token ASSIGN
%token ARROW
%token BACKQUOTE
%token COMMA
%token COLON
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
%token <string> UID_META
%token <string> UID_PAT
%token <Path.t> QID
%token <Path.t> ID_EXPL

// types

%start <Syntax.p_command> command
%start <Syntax.p_qident> id

%type <Syntax.p_ident> uid
%type <Syntax.p_path> path
%type <Syntax.p_ident option> patt
%type <Syntax.p_params> params

%type <Syntax.p_term> term
%type <Syntax.p_term> aterm
%type <Syntax.p_term> sterm

%type <Syntax.p_rule> rule
%type <Syntax.p_tactic> tactic
%type <Syntax.p_modifier> modifier
%type <Syntax.p_config> config
%type <Syntax.p_rw_patt> rw_patt
%type <Syntax.p_tactic list * Syntax.p_proof_end> proof

// Precedences listed from low to high

%nonassoc COMMA IN
%right ARROW

%%

uid: i=UID { make_pos $sloc i}

id:
  | p=QID { qid_of_path $sloc p}
  | i=UID { make_pos $sloc ([], i) }

term_id:
  | i=id { make_pos $sloc (P_Iden(i, false)) }
  | p=ID_EXPL { make_pos $sloc (P_Iden(qid_of_path $sloc p, true)) }

// Rewrite pattern identifier
patt: p=UID_PAT { if p = "_" then None else Some(make_pos $sloc p) }

// Identifiers for arguments
param_id:
  | i=uid { Some i }
  | WILD { None }

// Arguments of abstractions, products &c.
params:
  // Explicit argument without type annotation
  | x=param_id { ([x], None, false) }
  // Explicit argument with type annotation
  | L_PAREN xs=param_id+ COLON a=term R_PAREN
      { (xs, Some(a), false) }
  // Implicit argument (possibly with type annotation)
  | L_CU_BRACKET xs=param_id+ a=preceded(COLON, term)? R_CU_BRACKET
      { (xs, a, true) }

// Patterns of the rewrite tactic
rw_patt:
  | t=term { make_pos $sloc (P_rw_Term(t)) }
  | IN t=term { make_pos $sloc (P_rw_InTerm(t)) }
  | IN x=uid IN t=term { make_pos $sloc (P_rw_InIdInTerm(x, t)) }
  | u=term IN x=term t=preceded(IN, term)?
    {
      let ident_of_term {elt; _} =
        match elt with
          | P_Iden({elt=([], x); pos}, _) -> Pos.make pos x
          | _ -> $syntaxerror
      in
      match t with
      | Some(t) -> make_pos $sloc (P_rw_TermInIdInTerm(u, ident_of_term x, t))
      | None -> make_pos $sloc (P_rw_IdInTerm(ident_of_term u, x))
    }
  | u=term AS x=uid IN t=term
      { make_pos $sloc (P_rw_TermAsIdInTerm(u,x,t)) }

// Tactics available in proof mode.
tactic:
  | q=query { make_pos $sloc (P_tac_query q) }
  | APPLY t=term { make_pos $sloc (P_tac_apply t) }
  | ASSUME xs=param_id+ { make_pos $sloc (P_tac_assume xs) }
  | FAIL { make_pos $sloc P_tac_fail }
  | FOCUS i=INT { make_pos $sloc (P_tac_focus i) }
  | INDUCTION { make_pos $sloc P_tac_induction }
  | REFINE t=term { make_pos $sloc (P_tac_refine t) }
  | REFLEXIVITY { make_pos $sloc P_tac_refl }
  | REWRITE l=ASSOC? p=delimited(L_SQ_BRACKET, rw_patt, R_SQ_BRACKET)? t=term
    {
      let b =
        match l with
        | Some(Pratter.Left) -> false
        | _ -> true
      in
      make_pos $sloc (P_tac_rewrite(b,p,t))
    }
  | SIMPL { make_pos $sloc P_tac_simpl }
  | SOLVE { make_pos $sloc P_tac_solve }
  | SYMMETRY { make_pos $sloc P_tac_sym }
  | WHY3 s=STRINGLIT? { make_pos $sloc (P_tac_why3 s) }

// Modifiers of declarations.
modifier:
  | CONSTANT { make_pos $sloc (P_prop Tags.Const) }
  | INJECTIVE { make_pos $sloc (P_prop Tags.Injec) }
  | OPAQUE { make_pos $sloc P_opaq }
  | PRIVATE { make_pos $sloc (P_expo Tags.Privat) }
  | PROTECTED { make_pos $sloc (P_expo Tags.Protec) }
  | SEQUENTIAL { make_pos $sloc (P_mstrat Tags.Sequen) }

// Converts floats and integers to floats
float_or_int:
  | p=FLOAT { p }
  | n=INT   { float_of_int n }

// Configurations
config:
  // Add a builtin: [builtin "0" ≔ zero]
  | BUILTIN s=STRINGLIT ASSIGN i=id { P_config_builtin(s,i) }
  // Add an infix operator: [infix right 6.3 "+" ≔ plus]
  | INFIX a=ASSOC? p=float_or_int s=STRINGLIT ASSIGN i=id
      {
        let binop = (s, Option.get Pratter.Neither a, p, i) in
        P_config_binop(binop)
      }
  // Add a prefix operator: [prefix 1.2 "!" ≔ factorial]
  | PREFIX p=float_or_int s=STRINGLIT ASSIGN i=id
      { let unop = (s, p, i) in P_config_unop(unop) }
  | QUANTIFIER i=id { P_config_quant i }
  | UNIF_RULE r=unif_rule { P_config_unif_rule(r) }

assert_kw:
  | ASSERT { false }
  | ASSERT_NOT { true }

query:
  | k=assert_kw ps=params* TURNSTILE t=term COLON a=term
    {
      let t =
        if ps = [] then t else
        make_pos ($startpos(ps), $endpos(a)) (P_Abst(ps, t))
      in
      let a =
        if ps = [] then a else
        make_pos ($startpos(ps), $endpos(a)) (P_Prod(ps, a))
      in
      make_pos $sloc (P_query_assert(k, P_assert_typing(t, a)))
    }
  | k=assert_kw ps=params* TURNSTILE t=term EQUIV a=term
    {
      let t =
        if ps = [] then t else
        make_pos ($startpos(ps), $endpos(a)) (P_Abst(ps, t))
      in
      let a =
        if ps = [] then a else
        make_pos ($startpos(ps), $endpos(a)) (P_Abst(ps, a))
      in
      make_pos $sloc (P_query_assert(k, P_assert_conv(t, a)))
    }
  | COMPUTE t=term
    { make_pos $sloc (P_query_normalize(t, {strategy=SNF; steps=None})) }
  | PRINT i=id? { make_pos $sloc (P_query_print i) }
  | PROOFTERM { make_pos $sloc P_query_proofterm }
  | SET DEBUG fl=DEBUG_FLAGS
      { let (b, s) = fl in make_pos $sloc (P_query_debug(b, s)) }
  | SET FLAG s=STRINGLIT b=SWITCH { make_pos $sloc (P_query_flag(s,b)) }
  | SET PROVER s=STRINGLIT { make_pos $sloc (P_query_prover(s)) }
  | SET PROVER_TIMEOUT n=INT { make_pos $sloc (P_query_prover_timeout(n)) }
  | SET VERBOSE i=INT { make_pos $sloc (P_query_verbose(i)) }
  | TYPE_QUERY t=term
    { make_pos $sloc (P_query_infer(t, {strategy=NONE; steps=None}))}

proof_end:
  | ABORT { make_pos $sloc Syntax.P_proof_abort }
  | ADMIT { make_pos $sloc Syntax.P_proof_admit }
  | END { make_pos $sloc Syntax.P_proof_end }

proof: BEGIN ts=terminated(tactic, SEMICOLON)* pe=proof_end { ts, pe }

constructor:
  | i=uid xs=params* COLON t=term
    { let t = if xs = [] then t else
                make_pos ($startpos(xs), $endpos(t)) (P_Prod(xs,t))
      in (i,t) }

inductive:
  | i=uid xs=params* COLON t=term ASSIGN
    VBAR? l=separated_list(VBAR, constructor)
    { let t = if xs = [] then t else
                make_pos ($startpos(xs), $endpos(t)) (P_Prod(xs,t)) in
      make_pos $sloc (i,t,l) }

term_proof:
  | t=term { Some t, None }
  | p=proof { None, Some p }
  | t=term p=proof { Some t, Some p }

path: i=QID { make_pos $sloc i}

// Top level commands
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
      {
        let sym =
          {p_sym_mod=ms; p_sym_nam=s; p_sym_arg=al; p_sym_typ=Some(a);
           p_sym_trm=None; p_sym_def=false; p_sym_prf=po}
        in
        make_pos $sloc (P_symbol(sym))
      }
  | ms=modifier* SYMBOL s=uid al=params* ao=preceded(COLON, term)?
    ASSIGN tp=term_proof SEMICOLON
      {
        let sym =
          {p_sym_mod=ms; p_sym_nam=s; p_sym_arg=al; p_sym_typ=ao;
           p_sym_trm=fst tp; p_sym_prf=snd tp; p_sym_def=true}
        in
        make_pos $sloc (P_symbol(sym))
      }
  | ms=modifier* xs=params* INDUCTIVE
    is=separated_nonempty_list(WITH, inductive) SEMICOLON
      { make_pos $sloc (P_inductive(ms,xs,is)) }
  | RULE rs=separated_nonempty_list(WITH, rule) SEMICOLON
      { make_pos $sloc (P_rules(rs)) }
  | SET c=config SEMICOLON { make_pos $sloc (P_set(c)) }
  | q=query SEMICOLON { make_pos $sloc (P_query(q)) }
  | EOF { raise End_of_file }

// Environment of a metavariable or rewrite pattern
env: L_SQ_BRACKET ts=separated_list(SEMICOLON, term) R_SQ_BRACKET { ts }

// Atomic terms
aterm:
  | ti=term_id { ti }
  // The wildcard "_"
  | WILD { make_pos $sloc P_Wild }
  // The constant [TYPE] (of type Kind)
  | TYPE_TERM { make_pos $sloc P_Type }
  // Metavariable
  | m=UID_META e=env?
      {
        let mid = make_pos $loc(m) m in
        make_pos $sloc (P_Meta(mid, Option.map Array.of_list e))
      }
  // Pattern of rewrite rules
  | p=patt e=env? { make_pos $sloc (P_Patt(p, Option.map Array.of_list e)) }
  // Parentheses
  | L_PAREN t=term R_PAREN { make_pos $sloc (P_Wrap(t)) }
  // Explicitly given argument
  | L_CU_BRACKET t=term R_CU_BRACKET { make_pos $sloc (P_Expl(t)) }
  // Natural number
  | n=INT { make_pos $sloc (P_NLit(n)) }

// Symbolic terms (as with S-expressions)
sterm:
  | t=sterm u=aterm { make_pos $sloc (P_Appl(t,u)) }
  | t=aterm { t }

term:
  | t=sterm { t }
  | t=term ARROW u=term { make_pos $sloc (P_Arro(t, u)) }
  | BACKQUOTE q=term_id b=binder
    {
      let b = make_pos $loc(b) (P_Abst(fst b, snd b)) in
      make_pos $sloc (P_Appl(q, b))
    }
  | PI b=binder { make_pos $sloc (P_Prod(fst b, snd b)) }
  | LAMBDA b=binder { make_pos $sloc (P_Abst(fst b, snd b)) }
  | LET x=uid a=params* b=preceded(COLON, term)? ASSIGN t=term IN u=term
      { make_pos $sloc (P_LLet(x, a, b, t, u)) }

binder:
  | xs=params+ COMMA t=term { (xs, t) }
  | x=param_id COLON a=term COMMA t=term { ([[x], Some a, false], t) }

rule: l=term HOOK_ARROW r=term { make_pos $sloc (l, r) }

equation: l=term EQUIV r=term { (l, r) }

unif_rule: l=equation HOOK_ARROW
  L_SQ_BRACKET rs=separated_nonempty_list(SEMICOLON, equation) R_SQ_BRACKET
    {
      (* FIXME: give sensible positions instead of Pos.none and P.appl. *)
      let equiv = P.qiden LpLexer.unif_rule_path LpLexer.equiv in
      let cons = P.qiden LpLexer.unif_rule_path LpLexer.cons in
      let mk_equiv (l, r) = P.appl (P.appl equiv l) r in
      let lhs = mk_equiv l in
      let rs = List.map mk_equiv rs in
      let (r, rs) = List.(hd rs, tl rs) in
      let cat eqlst eq = P.appl (P.appl cons eq) eqlst in
      let rhs = List.fold_left cat r rs in
      make_pos $sloc (lhs, rhs)
    }

%%
