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
      let (mp, id) = List.split_last p in
      make_pos loc (mp, fst id)
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

%token <string * bool> ID
%token <string> ID_META
%token <string> ID_PAT
%token <(string * bool) list> QID
%token <(string * bool) list> QID_EXPL

// start symbols

%start <Syntax.p_command> command
%start ident

// types

%type <Syntax.p_term> term
%type <Syntax.p_term> aterm
%type <Syntax.p_term> sterm
%type <Syntax.p_args> arg_list
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

ident: i=ID { make_pos $sloc (fst i), snd i}

// [path] with a post processing to yield a [qident]
qident:
  | p=QID { qid_of_path $sloc p}
  | i=ID { make_pos $sloc ([], fst i) }

term_ident:
  | p=QID_EXPL
      { make_pos $sloc (P_Iden(qid_of_path $sloc p, true)) }
  | qid=qident { make_pos $sloc (P_Iden(qid, false)) }

// Rewrite pattern identifier
patt: p=ID_PAT { if p = "_" then None else Some(make_pos $sloc p) }

// Identifiers for arguments
argid:
  | i=ident { Some(fst i) }
  | WILD { None }

// Arguments of abstractions, products &c.
arg_list:
  // Explicit argument without type annotation
  | x=argid { ([x], None, false) }
  // Explicit argument with type annotation
  | L_PAREN xs=argid+ COLON a=term R_PAREN
      { (xs, Some(a), false) }
  // Implicit argument (possibly with type annotation)
  | L_CU_BRACKET xs=argid+ a=preceded(COLON, term)? R_CU_BRACKET
      { (xs, a, true) }

// Patterns of the rewrite tactic
rw_patt:
  | t=term { make_pos $sloc (P_rw_Term(t)) }
  | IN t=term { make_pos $sloc (P_rw_InTerm(t)) }
  | IN x=ident IN t=term { make_pos $sloc (P_rw_InIdInTerm(fst x, t)) }
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
  | u=term AS x=ident IN t=term
      { make_pos $sloc (P_rw_TermAsIdInTerm(u, fst x, t)) }

// Tactics available in proof mode.
tactic:
  | q=query { make_pos $sloc (P_tac_query q) }
  | APPLY t=term { make_pos $sloc (P_tac_apply t) }
  | ASSUME xs=argid+ { make_pos $sloc (P_tac_intro xs) }
  | FAIL { make_pos $sloc P_tac_fail }
  | FOCUS i=INT { make_pos $sloc (P_tac_focus i) }
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
  | BUILTIN s=STRINGLIT ASSIGN qid=qident { P_config_builtin(s, qid) }
  // Add an infix operator: [infix right 6.3 "+" ≔ plus]
  | INFIX a=ASSOC? p=float_or_int s=STRINGLIT ASSIGN qid=qident
      {
        let binop = (s, Option.get Pratter.Neither a, p, qid) in
        P_config_binop(binop)
      }
  // Add a prefix operator: [prefix 1.2 "!" ≔ factorial]
  | PREFIX p=float_or_int s=STRINGLIT ASSIGN qid=qident
      { let unop = (s, p, qid) in P_config_unop(unop) }
  | QUANTIFIER qid=qident { P_config_quant qid }
  | UNIF_RULE r=unif_rule { P_config_unif_rule(r) }

assert_kw:
  | ASSERT { false }
  | ASSERT_NOT { true }

query:
  | k=assert_kw ps=arg_list* TURNSTILE t=term COLON a=term
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
  | k=assert_kw ps=arg_list* TURNSTILE t=term EQUIV a=term
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
  | PRINT qid=qident? { make_pos $sloc (P_query_print qid) }
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
  | i=ident xs=arg_list* COLON t=term
    { let t = if xs = [] then t else
                make_pos ($startpos(xs), $endpos(t)) (P_Prod(xs,t))
      in (i,t) }

inductive:
  | i=ident xs=arg_list* COLON t=term ASSIGN
    VBAR? l=separated_list(VBAR, constructor)
    { let t = if xs = [] then t else
                make_pos ($startpos(xs), $endpos(t)) (P_Prod(xs,t)) in
      let l = List.map (fun (i,t) -> (fst i,t)) l in
      make_pos $sloc (fst i, t, l)
      }

term_proof:
  | t=term { Some t, None }
  | p=proof { None, Some p }
  | t=term p=proof { Some t, Some p }

// Top level commands
command:
  | REQUIRE OPEN p=QID+ SEMICOLON { make_pos $sloc (P_require(true,p)) }
  | REQUIRE p=QID+ SEMICOLON { make_pos $sloc (P_require(false, p)) }
  | REQUIRE p=QID AS a=ident SEMICOLON
      {
        let alias = Pos.make (fst a).pos ((fst a).elt, snd a) in
        make_pos $sloc (P_require_as(p, alias))
      }
  | OPEN p=QID SEMICOLON { make_pos $sloc (P_open([p])) }
  | ms=modifier* SYMBOL s=ident al=arg_list* COLON a=term
    po=proof? SEMICOLON
      {
        let sym =
          {p_sym_mod=ms; p_sym_nam=fst s; p_sym_arg=al; p_sym_typ=Some(a);
           p_sym_trm=None; p_sym_def=false; p_sym_prf=po}
        in
        make_pos $sloc (P_symbol(sym))
      }
  | ms=modifier* SYMBOL s=ident al=arg_list* ao=preceded(COLON, term)?
    ASSIGN tp=term_proof SEMICOLON
      {
        let sym =
          {p_sym_mod=ms; p_sym_nam=fst s; p_sym_arg=al; p_sym_typ=ao;
           p_sym_trm=fst tp; p_sym_prf=snd tp; p_sym_def=true}
        in
        make_pos $sloc (P_symbol(sym))
      }
  | ms=modifier* xs=arg_list* INDUCTIVE
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
  | ti=term_ident { ti }
  // The wildcard "_"
  | WILD { make_pos $sloc P_Wild }
  // The constant [TYPE] (of type Kind)
  | TYPE_TERM { make_pos $sloc P_Type }
  // Metavariable
  | m=ID_META e=env?
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
  | t=term ARROW u=term { make_pos $sloc (P_Impl(t, u)) }
  // Quantifier
  | BACKQUOTE q=term_ident b=binder
      {
        let bder = Pos.make b.pos (P_Abst(fst b.elt, snd b.elt)) in
        make_pos $sloc (P_Appl(q, bder))
      }
  | PI b=binder { make_pos $sloc (P_Prod(fst b.elt, snd b.elt)) }
  | LAMBDA b=binder { make_pos $sloc (P_Abst(fst b.elt, snd b.elt)) }
  | LET x=ident a=arg_list* b=preceded(COLON, term)? ASSIGN t=term IN u=term
      { make_pos $sloc (P_LLet(fst x, a, b, t, u)) }

/* REVIEW: allow pattern of the form \x y z: N, t */
binder:
  | xs=arg_list+ COMMA t=term
      { make_pos $sloc (xs, t) }
  | x=argid COLON a=term COMMA t=term
      { make_pos $sloc ([[x], Some a, false], t) }

// A rewrite rule [lhs ↪ rhs]
rule: l=term HOOK_ARROW r=term { make_pos $sloc (l, r) }

equation: l=term EQUIV r=term { (l, r) }

unif_rule: l=equation HOOK_ARROW
L_SQ_BRACKET rs=separated_nonempty_list(SEMICOLON, equation) R_SQ_BRACKET
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
      make_pos $sloc (lhs, rhs)
    }

%%
