(* Lambdapi Menhir parser. We need to parse UTF8 - and hence use Sedlex. *)
(* Using Sedlex (and not Ocamllex) requires to use the "revised" API of Menhir*)
(* which abstracts the Lexing buffer. *)
%{
    open Syntax
    open Pos
    open Extra

    let make_pos : Lexing.position * Lexing.position -> 'a -> 'a Pos.loc =
      fun lps elt -> {pos = Some(locate lps); elt}

    let rev_tl : (string * bool) list -> p_module_path * string = fun p ->
      match List.rev p with
      | hd :: tl -> (List.rev tl, fst hd)
      | [] -> assert false

    (** [sanity_check pos s] checks that the token [s] is appropriate for an
        infix operator or a declared identifier. If it is not the case, then the
        [Fatal] exception is raised. *)
    let sanity_check : Pos.pos -> string -> unit = fun _ _ -> assert false
 %}

%token EOF

// Command keywords
%token THEOREM
%token COLON
%token SYMBOL
%token RULE
%token WITH
%token OPEN
%token REQUIRE
%token AS
%token DEFINITION
%token REWRITE
// Other commands and utils
%token PREFIX
%token SET
%token BUILTIN
%token <assoc> ASSOC
%token INFIX
%token VERBOSE
%token FLAG
%token PROVER
%token PROVER_TIMEOUT
%token COMPUTE
%token COMPUTE_TYPE
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
// Terms
%token ARROW
%token COMMA
// Sigils
%token AT
%token DOLLAR
%token QUESTION_MARK
%token DOT
%token ASSIGN
%token WILD
%token LAMBDA
%token PI
%token LET
%token IN
%token L_PAREN
%token R_PAREN
%token L_CU_BRACKET
%token R_CU_BRACKET
%token L_SQ_BRACKET
%token R_SQ_BRACKET
%token SEMICOLON
%token TYPE
// Proofs
%token PROOF
%token <p_proof_end> PROOF_END
// Tactics
%token INTRO
%token APPLY
%token SIMPL
// Identifiers
%token <string * bool> ID

%start <Syntax.p_command> command
%type <Syntax.p_term> term
%type <Syntax.p_term> aterm
%type <Syntax.p_term> sterm
%type <Syntax.p_arg> arg
%type <Syntax.ident * bool> ident
%type <Syntax.ident option> patt
%type <Syntax.p_rule> rule
%type <Syntax.p_tactic> tactic
%type <Syntax.p_modifier loc> modifier
%type <Syntax.p_module_path> path
%type <Syntax.p_config> config
%type <Syntax.qident> qident
%type <Syntax.p_rw_patt> rw_patt_spec

// Precedences listed from low to high
%nonassoc IN
%left COMMA
%right ARROW

%%

ident: i=ID { (make_pos $loc (fst i), snd i) }

path: ms=separated_nonempty_list(DOT, ID) { ms }

// [path] with a post processing
qident: p=path { let qid = rev_tl p in make_pos $loc(p) qid }

// Rewrite pattern identifier (without the sigil)
patt: DOLLAR p=ident { if (fst p).elt = "_" then None else Some(fst p) }

arg_ident:
  | i=ident { Some(fst i) }
  | WILD { None }

arg:
  // Explicit argument without type annotation
  | x=arg_ident { ([x], None, false) }
  // Explicit argument with type annotation
  | L_PAREN xs=arg_ident+ COLON a=term R_PAREN
      { (xs, Some(a), false) }
  // Implicit argument (possibly with type annotation)
  | L_CU_BRACKET xs=arg_ident+ a=preceded(COLON, term)? R_CU_BRACKET
      { (xs, a, true) }

rw_patt_spec:
  | t=term { P_rw_Term(t) }
  | IN t=term { P_rw_InTerm(t) }
  | IN x=ident IN t=term { P_rw_InIdInTerm(fst x, t) }
  /* | x=ident IN t=term { P_rw_IdInTerm(fst x, t) } */
  | u=term IN x=ident IN t=term { P_rw_TermInIdInTerm(u, fst x, t) }
  | u=term AS x=ident IN t=term { P_rw_TermAsIdInTerm(u, fst x, t) }

rw_patt: L_SQ_BRACKET r=rw_patt_spec R_SQ_BRACKET { make_pos $loc r }

tactic:
  | INTRO xs=arg_ident+ { make_pos $loc (P_tac_intro(xs)) }
  | APPLY t=term { make_pos $loc (P_tac_apply(t)) }
  | SIMPL { make_pos $loc P_tac_simpl }
  | REWRITE p=rw_patt? t=term { make_pos $loc (P_tac_rewrite(true,p,t)) }

modifier:
  | CONSTANT { make_pos $loc (P_prop(Terms.Const)) }
  | INJECTIVE { make_pos $loc (P_prop(Terms.Injec)) }
  | PROTECTED { make_pos $loc (P_expo(Terms.Protec)) }
  | PRIVATE { make_pos $loc (P_expo(Terms.Privat)) }
  | SEQUENTIAL { make_pos $loc (P_mstrat(Terms.Sequen)) }

// Marker of end of proof
prfend: p=PROOF_END { make_pos $loc p }

statement:
  THEOREM s=ident al=arg* COLON a=term PROOF { make_pos $loc (fst s, al, a) }

config:
  | BUILTIN s=STRINGLIT ASSIGN qid=qident { P_config_builtin(s, qid) }
  | PREFIX p=FLOAT s=STRINGLIT ASSIGN qid=qident
      {
        let unop = (s, p, qid) in
        sanity_check (locate $loc(s)) s;
        P_config_unop(unop)
      }
  | INFIX a=ASSOC? p=FLOAT s=STRINGLIT ASSIGN qid=qident
      {
        let binop = (s, Option.get Assoc_none a, p, qid) in
        sanity_check (locate $loc(s)) s;
        P_config_binop(binop)
      }

query:
  | SET VERBOSE i=INT { make_pos $loc (P_query_verbose(i)) }
  | SET FLAG s=STRINGLIT b=SWITCH { make_pos $loc (P_query_flag(s,b)) }
  | COMPUTE_TYPE t=term
    { make_pos $loc (P_query_infer(t, {strategy=NONE; steps=None}))}
  | COMPUTE t=term
    { make_pos $loc (P_query_normalize(t, {strategy=SNF; steps=None})) }
  | SET PROVER s=STRINGLIT { make_pos $loc (P_query_prover(s)) }
  | SET PROVER_TIMEOUT n=INT { make_pos $loc (P_query_prover_timeout(n)) }

command:
  | REQUIRE OPEN p=path+ SEMICOLON { make_pos $loc (P_require(true,p)) }
  | REQUIRE p=path+ SEMICOLON { make_pos $loc (P_require(false, p)) }
  | REQUIRE p=path AS a=ident SEMICOLON
      {
        let alias = Pos.make (fst a).pos ((fst a).elt, snd a) in
        make_pos $loc (P_require_as(p, alias))
      }
  | OPEN p=path SEMICOLON { make_pos $loc (P_open([p])) }
  | ms=modifier* SYMBOL s=ident al=arg* COLON a=term SEMICOLON
      { make_pos $loc (P_symbol(ms, fst s, al, a)) }
  | ms=modifier* DEFINITION s=ident al=arg* ao=preceded(COLON, term)?
    ASSIGN b=term SEMICOLON
      { make_pos $loc (P_definition(ms, false, fst s, al, ao, b))}
  | ms=modifier* st=statement ts=tactic* pe=prfend
      { make_pos $loc (P_theorem(ms, st, ts, pe)) }
  | RULE rs=separated_nonempty_list(WITH, rule) SEMICOLON
      { make_pos $loc (P_rules(rs)) }
  | SET c=config SEMICOLON { make_pos $loc (P_set(c)) }
  | q=query SEMICOLON { make_pos $loc (P_query(q)) }
  | EOF { raise End_of_file }

// Environment of a metavariable or rewrite pattern
env: L_SQ_BRACKET ts=separated_list(SEMICOLON, term) R_SQ_BRACKET { ts }

sterm:
  // Explicited identifier (with @)
  | AT qid=qident { make_pos $loc (P_Iden(qid, true)) }
  // Qualified identifier
  | qid=qident { make_pos $loc (P_Iden(qid, false)) }
  // The wildcard "_"
  | WILD { make_pos $loc P_Wild }
  | TYPE { make_pos $loc P_Type }
  // Metavariable
  | QUESTION_MARK m=ident e=env?
      { make_pos $loc (P_Meta(fst m, Option.map Array.of_list e)) }
  // Pattern of rewrite rules
  | p=patt e=env? { make_pos $loc (P_Patt(p, Option.map Array.of_list e)) }
  // Parentheses
  | L_PAREN t=term R_PAREN { make_pos $loc (P_Wrap(t)) }
  // Explicitly given argument
  | L_CU_BRACKET t=term R_CU_BRACKET { make_pos $loc (P_Expl(t)) }

// Applied terms
aterm:
  | t=aterm u=sterm { make_pos $loc (P_Appl(t,u)) }
  | t=sterm { t }

term:
  | t=aterm { t }
  | t=term ARROW u=term { make_pos $loc (P_Impl(t, u)) }
  | PI xs=arg+ COMMA b=term { make_pos $loc (P_Prod(xs, b)) }
  | LAMBDA xs=arg+ COMMA t=term { make_pos $loc (P_Abst(xs, t)) }
  | LET x=ident a=arg* b=preceded(COLON, term)? ASSIGN t=term IN u=term
      { make_pos $loc (P_LLet(fst x, a, b, t, u)) }

rule: l=term REWRITE r=term { make_pos $loc (l, r) }

%%
