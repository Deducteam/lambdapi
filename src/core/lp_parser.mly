(* Lambdapi Menhir parser. We need to parse UTF8 - and hence use Sedlex. *)
(* Using Sedlex (and not Ocamllex) requires to use the "revised" API of Menhir*)
(* which abstracts the Lexing buffer. *)
%{
    open Syntax
    open Pos
    open Extra

    let make_pos : Lexing.position * Lexing.position -> 'a -> 'a Pos.loc =
      fun lps elt -> {pos = Some(locate lps); elt}
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
%token ABORT
%token ADMIT
%token QED
// Tactics
%token INTRO
%token APPLY
%token SIMPL
// Identifiers
%token <string * bool> ID
%token <Syntax.p_module_path * string> QID

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

// Precedences listed from low to high
%nonassoc IN
%left COMMA
%right ARROW

%%

ident: i=ID { (make_pos $loc (fst i), snd i) }

qident: qid=QID { make_pos $loc qid }

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

tactic:
  | INTRO xs=arg_ident+ { make_pos $loc (P_tac_intro(xs)) }
  | APPLY t=term { make_pos $loc (P_tac_apply(t)) }
  | SIMPL { make_pos $loc P_tac_simpl }

modifier:
  | CONSTANT { make_pos $loc (P_prop(Terms.Const)) }
  | INJECTIVE { make_pos $loc (P_prop(Terms.Injec)) }
  | PROTECTED { make_pos $loc (P_expo(Terms.Protec)) }
  | PRIVATE { make_pos $loc (P_expo(Terms.Privat)) }
  | SEQUENTIAL { make_pos $loc (P_mstrat(Terms.Sequen)) }

// Marker of end of proof
prfend:
  | QED { make_pos $loc P_proof_qed }
  | ADMIT { make_pos $loc P_proof_admit }
  | ABORT { make_pos $loc P_proof_abort }

// Theorem statement REVIEW: can it be inlined?
statement:
  THEOREM s=ident al=arg* COLON a=term PROOF { make_pos $loc (fst s, al, a) }

command:
  // REVIEW: is it correct to use qident? Answer: it is, according to the
  // documented BNF where path and qident are the same regular expressions.
  | REQUIRE p=qident DOT { make_pos $loc (P_require(false, [fst p.elt])) }
  | REQUIRE OPEN p=qident DOT { make_pos $loc (P_require(true,[fst p.elt])) }
  | REQUIRE qid=qident AS p=ident DOT
      {
        let alias = Pos.make (fst p).pos ((fst p).elt, snd p) in
        make_pos $loc (P_require_as(fst qid.elt, alias))
      }
  | OPEN qid=qident { make_pos $loc (P_open([fst qid.elt])) }
  | ms=modifier* SYMBOL s=ident al=arg* COLON a=term DOT
      { make_pos $loc (P_symbol(ms, fst s, al, a)) }
  | ms=modifier* DEFINITION s=ident al=arg* ao=preceded(COLON, term)?
    ASSIGN b=term DOT
      { make_pos $loc (P_definition(ms, false, fst s, al, ao, b))}
  | ms=modifier* st=statement ts=tactic* pe=prfend
      { make_pos $loc (P_theorem(ms, st, ts, pe)) }
  | RULE r=rule rs=preceded(WITH, rule)* DOT { make_pos $loc (P_rules(r::rs)) }
  | EOF { raise End_of_file }

// Environment of a metavariable or rewrite pattern
env: L_SQ_BRACKET ts=separated_list(SEMICOLON, term) R_SQ_BRACKET { ts }

sterm:
  // Explicited identifier (with @)
  | AT qid=qident { make_pos $loc (P_Iden(qid, true)) }
  // Qualified identifier
  | qid=qident { make_pos $loc (P_Iden(qid, false)) }
  // Identifier
  | id=ident
      { make_pos $loc (P_Iden(Pos.map (fun i -> ([], i)) (fst id), false)) }
  // The wildcard "_"
  | WILD { make_pos $loc P_Wild }
  | TYPE { make_pos $loc P_Type }
  // Metavariable
  | QUESTION_MARK m=ident e=env?
      { make_pos $loc (P_Meta(fst m, Option.map Array.of_list e)) }
  // Pattern of rewrite rules
  | p=patt e=env? { make_pos $loc (P_Patt(p, Option.map Array.of_list e)) }
  // Parentheses
  | L_PAREN t=term R_PAREN { t }
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
