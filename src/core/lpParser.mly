(* Lambdapi Menhir parser. We need to parse UTF8 - and hence use Sedlex.
   Using Sedlex (and not Ocamllex) requires to use the "revised" API of
   Menhir which abstracts the Lexing buffer. *)
%{
    open Syntax
    open Lplib
    open Pos

    let make_pos : Lexing.position * Lexing.position -> 'a -> 'a loc =
      fun lps elt -> Pos.in_pos (locate lps) elt

    let qid_of_path loc p =
      let (mp, id) = List.split_last p in
      make_pos loc (mp, fst id)
 %}

%token EOF

// Command keywords
%token COLON
%token SYMBOL
%token INDUCTIVE
%token RULE
%token WITH
%token OPEN
%token REQUIRE
%token AS
%token REWRITE
// Queries
%token SET
%token ASSERT
%token ASSERT_NOT
// Other commands and utils
%token PREFIX
%token BUILTIN
%token <Pratter.associativity> ASSOC
%token INFIX
%token QUANTIFIER
%token VERBOSE
%token FLAG
%token PROVER
%token PROVER_TIMEOUT
%token COMPUTE
%token COMPUTE_TYPE
%token EQUIV
%token UNIF_RULE
%token <bool * string> DEBUG_FLAGS
%token <bool> SWITCH
%token <string> STRINGLIT
%token <int> INT
%token <float> FLOAT
// Modifiers
%token CONSTANT
%token INJECTIVE
%token PROTECTED
%token PRIVATE
%token SEQUENTIAL
%token OPAQUE
// Terms
%token ARROW
%token COMMA
// Sigils
%token VBAR
%token TURNSTILE
%token ASSIGN
%token WILD
%token LAMBDA
%token PI
%token LET
%token IN
%token BACKQUOTE
%token L_PAREN
%token R_PAREN
%token L_CU_BRACKET
%token R_CU_BRACKET
%token L_SQ_BRACKET
%token R_SQ_BRACKET
%token SEMICOLON
%token TYPE
// Proofs
%token BEGIN
%token END
%token ABORT
%token ADMIT
// Tactics
%token INTRO
%token APPLY
%token SIMPL
%token REFL
%token REFINE
%token SYMMETRY
%token WHY3
%token PROOFTERM
%token PRINT
%token FAIL
// Identifiers
%token <(string * bool) list> PATH
%token <string * bool> ID
%token <string> ID_PAT
%token <string> ID_META
%token <string> ID_EXPL
%token <(string * bool) list> QID_EXPL

%start <Syntax.p_command> command
%start ident
%type <Syntax.p_term> term
%type <Syntax.p_term> aterm
%type <Syntax.p_term> sterm
%type <Syntax.p_args> arg
%type <Syntax.ident * bool> ident
%type <Syntax.ident option> patt
%type <Syntax.p_rule> rule
%type <Syntax.p_tactic> tactic
%type <Syntax.p_modifier> modifier
%type <Syntax.p_config> config
%type <Syntax.qident> qident
%type <Syntax.p_rw_patt> rw_patt
%type <Syntax.p_tactic list * Syntax.p_proof_end> proof

// Precedences listed from low to high
%nonassoc COMMA IN
%right ARROW

%%

ident: i=ID { make_pos $loc (fst i), snd i}

// [path] with a post processing to yield a [qident]
qident:
  | p=PATH { qid_of_path $loc p}
  | i=ID { make_pos $loc ([], fst i) }

term_ident:
  | p=QID_EXPL
      { make_pos $loc (P_Iden(qid_of_path $loc p, true)) }
  | qid=qident { make_pos $loc (P_Iden(qid, false)) }
  | id=ID_EXPL
      {
        let id = make_pos $loc ([], id) in
        make_pos $loc (P_Iden(id, true))
      }

// Rewrite pattern identifier
patt: p=ID_PAT { if p = "_" then None else Some(make_pos $loc p) }

// Identifiers for arguments
arg_ident:
  | i=ident { Some(fst i) }
  | WILD { None }

// Arguments of abstractions, products &c.
arg:
  // Explicit argument without type annotation
  | x=arg_ident { ([x], None, false) }
  // Explicit argument with type annotation
  | L_PAREN xs=arg_ident+ COLON a=term R_PAREN
      { (xs, Some(a), false) }
  // Implicit argument (possibly with type annotation)
  | L_CU_BRACKET xs=arg_ident+ a=preceded(COLON, term)? R_CU_BRACKET
      { (xs, a, true) }

// Patterns of the rewrite tactic
rw_patt:
  | t=term { make_pos $loc (P_rw_Term(t)) }
  | IN t=term { make_pos $loc (P_rw_InTerm(t)) }
  | IN x=ident IN t=term { make_pos $loc (P_rw_InIdInTerm(fst x, t)) }
  | u=term IN x=term t=preceded(IN, term)?
    {
      let ident_of_term {elt; _} =
        match elt with
          | P_Iden({elt=([], x); pos}, _) -> Pos.make pos x
          | _ -> $syntaxerror
      in
      match t with
      | Some(t) -> make_pos $loc (P_rw_TermInIdInTerm(u, ident_of_term x, t))
      | None -> make_pos $loc (P_rw_IdInTerm(ident_of_term u, x))
    }
  | u=term AS x=ident IN t=term
      { make_pos $loc (P_rw_TermAsIdInTerm(u, fst x, t)) }

// Tactics available in proof mode.
tactic:
  | INTRO xs=arg_ident+ { make_pos $loc (P_tac_intro(xs)) }
  | APPLY t=term { make_pos $loc (P_tac_apply(t)) }
  | SIMPL { make_pos $loc P_tac_simpl }
  | REWRITE l=ASSOC? p=delimited(L_SQ_BRACKET, rw_patt, R_SQ_BRACKET)? t=term
    {
      let b =
        match l with
        | Some(Pratter.Left) -> false
        | _ -> true
      in
      make_pos $loc (P_tac_rewrite(b,p,t))
    }
  | REFINE t=term { make_pos $loc (P_tac_refine(t)) }
  | REFL { make_pos $loc P_tac_refl }
  | SYMMETRY { make_pos $loc P_tac_sym }
  | WHY3 s=STRINGLIT? { make_pos $loc (P_tac_why3(s)) }
  | q=query { make_pos $loc (P_tac_query(q)) }
  | FAIL { make_pos $loc P_tac_fail }

// Modifiers of declarations.
modifier:
  | CONSTANT { make_pos $loc (P_prop(Terms.Const)) }
  | INJECTIVE { make_pos $loc (P_prop(Terms.Injec)) }
  | PROTECTED { make_pos $loc (P_expo(Terms.Protec)) }
  | PRIVATE { make_pos $loc (P_expo(Terms.Privat)) }
  | SEQUENTIAL { make_pos $loc (P_mstrat(Terms.Sequen)) }
  | OPAQUE { make_pos $loc (P_opaq) }

// Converts floats and integers to floats
float_of_int:
  | p=FLOAT { p }
  | n=INT   { float_of_int n }

// Configurations
config:
  // Add a builtin: [builtin "0" ≔ zero]
  | BUILTIN s=STRINGLIT ASSIGN qid=qident { P_config_builtin(s, qid) }
  // Add a prefix operator: [prefix 1.2 "!" ≔ factorial]
  | PREFIX p=float_of_int s=STRINGLIT ASSIGN qid=qident
      { let unop = (s, p, qid) in P_config_unop(unop) }
  // Add an infix operator: [infix right 6.3 "+" ≔ plus]
  | INFIX a=ASSOC? p=float_of_int s=STRINGLIT ASSIGN qid=qident
      {
        let binop = (s, Option.get Pratter.Neither a, p, qid) in
        P_config_binop(binop)
      }
  | QUANTIFIER qid=qident { P_config_quant qid }
  | UNIF_RULE r=unif_rule { P_config_unif_rule(r) }

assert_not:
  | ASSERT { false }
  | ASSERT_NOT { true }

query:
  // Set verbosity level
  | SET VERBOSE i=INT { make_pos $loc (P_query_verbose(i)) }
  | SET FLAG s=STRINGLIT b=SWITCH { make_pos $loc (P_query_flag(s,b)) }
  | SET fl=DEBUG_FLAGS
      { let (b, s) = fl in make_pos $loc (P_query_debug(b, s)) }
  | COMPUTE_TYPE t=term
    { make_pos $loc (P_query_infer(t, {strategy=NONE; steps=None}))}
  | COMPUTE t=term
    { make_pos $loc (P_query_normalize(t, {strategy=SNF; steps=None})) }
  | SET PROVER s=STRINGLIT { make_pos $loc (P_query_prover(s)) }
  | SET PROVER_TIMEOUT n=INT { make_pos $loc (P_query_prover_timeout(n)) }
  | k=assert_not ps=arg* TURNSTILE t=term COLON a=term
    {
      let t =
        if ps = [] then t else
        make_pos ($startpos(ps), $endpos(a)) (P_Abst(ps, t))
      in
      let a =
        if ps = [] then a else
        make_pos ($startpos(ps), $endpos(a)) (P_Prod(ps, a))
      in
      make_pos $loc (P_query_assert(k, P_assert_typing(t, a)))
    }
  | k=assert_not ps=arg* TURNSTILE t=term EQUIV a=term
    {
      let t =
        if ps = [] then t else
        make_pos ($startpos(ps), $endpos(a)) (P_Abst(ps, t))
      in
      let a =
        if ps = [] then a else
        make_pos ($startpos(ps), $endpos(a)) (P_Abst(ps, a))
      in
      make_pos $loc (P_query_assert(k, P_assert_conv(t, a)))
    }
  | PRINT qid=qident? { make_pos $loc (P_query_print qid) }
  | PROOFTERM { make_pos $loc P_query_proofterm }

proof_end:
  | END { make_pos $loc Syntax.P_proof_end }
  | ADMIT { make_pos $loc Syntax.P_proof_admit }
  | ABORT { make_pos $loc Syntax.P_proof_abort }

proof: BEGIN ts=terminated(tactic, SEMICOLON)* pe=proof_end { ts, pe }

inductive:
  | i=ident COLON t=term ASSIGN VBAR?
c=separated_list(VBAR, separated_pair(ident, COLON, term))
      {
        let c = List.map (fun (id, t) -> (fst id, t)) c in
        make_pos $loc (fst i, t, c)
      }


// Top level commands
command:
  | REQUIRE OPEN p=PATH+ SEMICOLON { make_pos $loc (P_require(true,p)) }
  | REQUIRE p=PATH+ SEMICOLON { make_pos $loc (P_require(false, p)) }
  | REQUIRE p=PATH AS a=ident SEMICOLON
      {
        let alias = Pos.make (fst a).pos ((fst a).elt, snd a) in
        make_pos $loc (P_require_as(p, alias))
      }
  | OPEN p=PATH SEMICOLON { make_pos $loc (P_open([p])) }
  | ms=modifier* SYMBOL s=ident al=arg* COLON a=term SEMICOLON
      {
        let sym =
          {p_sym_mod=ms; p_sym_nam=fst s; p_sym_arg=al; p_sym_typ=Some(a);
           p_sym_trm=None; p_sym_def=false; p_sym_prf=None}
        in
        make_pos $loc (P_symbol(sym))
      }
  | ms=modifier* SYMBOL s=ident al=arg* ao=preceded(COLON, term)? p=proof
      {
        let sym =
            {p_sym_mod=ms; p_sym_nam=fst s; p_sym_arg=al; p_sym_typ=ao;
             p_sym_trm=None; p_sym_def=false; p_sym_prf=Some(p)}
          in
          make_pos $loc (P_symbol(sym))
      }
  | ms=modifier* SYMBOL s=ident al=arg* ao=preceded(COLON, term)?
    ASSIGN de=term? SEMICOLON
      {
        let sym =
          {p_sym_mod=ms; p_sym_nam=fst s; p_sym_arg=al; p_sym_typ=ao;
           p_sym_trm=de; p_sym_prf=None; p_sym_def=true}
        in
        make_pos $loc (P_symbol(sym))
      }
  | ms=modifier* SYMBOL s=ident al=arg* ao=preceded(COLON, term)?
    ASSIGN de=term? p=proof
      {
        let sym =
          {p_sym_mod=ms; p_sym_nam=fst s; p_sym_arg=al; p_sym_typ=ao;
           p_sym_trm=de; p_sym_prf=Some(p); p_sym_def=true}
        in
        make_pos $loc (P_symbol(sym))
      }
  | ms=modifier* INDUCTIVE is=separated_nonempty_list(WITH, inductive)
    SEMICOLON
      { make_pos $loc (P_inductive(ms, is)) }
  | RULE rs=separated_nonempty_list(WITH, rule) SEMICOLON
      { make_pos $loc (P_rules(rs)) }
  | SET c=config SEMICOLON { make_pos $loc (P_set(c)) }
  | q=query SEMICOLON { make_pos $loc (P_query(q)) }
  | EOF { raise End_of_file }

// Environment of a metavariable or rewrite pattern
env: L_SQ_BRACKET ts=separated_list(SEMICOLON, term) R_SQ_BRACKET { ts }

// Atomic terms
aterm:
  | ti=term_ident { ti }
  // The wildcard "_"
  | WILD { make_pos $loc P_Wild }
  // The constant [TYPE] (of type Kind)
  | TYPE { make_pos $loc P_Type }
  // Metavariable
  | m=ID_META e=env?
      {
        let mid = make_pos $loc(m) m in
        make_pos $loc (P_Meta(mid, Option.map Array.of_list e))
      }
  // Pattern of rewrite rules
  | p=patt e=env? { make_pos $loc (P_Patt(p, Option.map Array.of_list e)) }
  // Parentheses
  | L_PAREN t=term R_PAREN { make_pos $loc (P_Wrap(t)) }
  // Explicitly given argument
  | L_CU_BRACKET t=term R_CU_BRACKET { make_pos $loc (P_Expl(t)) }
  // Natural number
  | n=INT { make_pos $loc (P_NLit(n)) }

// Symbolic terms (as with S-expressions)
sterm:
  | t=sterm u=aterm { make_pos $loc (P_Appl(t,u)) }
  | t=aterm { t }

term:
  | t=sterm { t }
  | t=term ARROW u=term { make_pos $loc (P_Impl(t, u)) }
  // Quantifier
  | BACKQUOTE q=term_ident b=binder
      {
        let bder = Pos.make b.pos (P_Abst(fst b.elt, snd b.elt)) in
        make_pos $loc (P_Appl(q, bder))
      }
  | PI b=binder { make_pos $loc (P_Prod(fst b.elt, snd b.elt)) }
  | LAMBDA b=binder { make_pos $loc (P_Abst(fst b.elt, snd b.elt)) }
  | LET x=ident a=arg* b=preceded(COLON, term)? ASSIGN t=term IN u=term
      { make_pos $loc (P_LLet(fst x, a, b, t, u)) }

/* REVIEW: allow pattern of the form \x y z: N, t */
binder:
  | xs=arg+ COMMA t=term
      { make_pos $loc (xs, t) }
  | x=arg_ident COLON a=term COMMA t=term
      { make_pos $loc ([[x], Some a, false], t) }

// A rewrite rule [lhs ↪ rhs]
rule: l=term REWRITE r=term { make_pos $loc (l, r) }

equation: l=term EQUIV r=term { (l, r) }

unif_rule: l=equation REWRITE
BEGIN rs=separated_nonempty_list(SEMICOLON, equation) END
    {
      let equiv = Pos.none (P_Iden(Pos.none ([], "#equiv"), true)) in
      let p_appl t u = Pos.none (P_Appl(t, u)) in
      let mkequiv (l, r) = p_appl (p_appl equiv l) r in
      let lhs = mkequiv l in
      let cons = Pos.none (P_Iden(Pos.none ([], "#cons"), true)) in
      let rs = List.map mkequiv rs in
      let (r, rs) = List.(hd rs, tl rs) in
      let cat eqlst eq = p_appl (p_appl cons eq) eqlst in
      let rhs = List.fold_left cat r rs in
      make_pos $loc (lhs, rhs)
    }

%%
