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
%token AT
%token DOT
%token ARROW
%token COMMA
%token COLON
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
%token THEOREM
%token TYPE
%token SYMBOL
%token RULE
%token WITH
%token OPEN
%token REQUIRE
%token AS
%token DEFINITION
%token REWRITE
%token CONSTANT
%token INJECTIVE
%token PROTECTED
%token PRIVATE
%token PROOF
%token ABORT
%token ADMIT
%token QED
%token INTRO
%token SEQUENTIAL
%token <string> META
%token <string> PATT
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

// Precedences listed from low to high
%nonassoc IN
%left COMMA
%right ARROW

%%

ident:
  | i=ID { (make_pos $loc (fst i), snd i) }

qident:
  | qid=QID { make_pos $loc qid }

// Meta variable identifier (without sigil)
// FIXME: what happens if meta is "_"?
meta:
  | m=META { make_pos $loc m }

// Rewrite pattern identifier (without the sigil)
patt:
  | p=PATT { if p = "_" then None else Some(make_pos $loc p) }

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
  | THEOREM s=ident al=arg* COLON a=term PROOF { make_pos $loc (fst s, al, a) }
proof: ts=tactic* e=prfend { (ts, e) } // REVIEW: can it be inlined?

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
  | ms=modifier* st=statement prf=proof
      { let (ts, pe) = prf in make_pos $loc (P_theorem(ms, st, ts, pe)) }
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
  | m=meta e=env? { make_pos $loc (P_Meta(m, Option.map Array.of_list e)) }
  // Pattern of rewrite rules
  | p=patt e=env? { make_pos $loc (P_Patt(p, Option.map Array.of_list e)) }
  // Parentheses
  | L_PAREN t=term R_PAREN { t }
  // Explicitly given argument
  | L_CU_BRACKET t=term R_CU_BRACKET { make_pos $loc (P_Expl(t)) }

aterm:
  | t=aterm u=sterm { make_pos $loc (P_Appl(t,u)) }
  | t=sterm { t }

term:
  | t=aterm { t }
  | t=term ARROW u=term { make_pos $loc (P_Impl(t, u)) }
  | PI xs=arg+ COMMA b=term { make_pos $loc (P_Prod(xs, b)) }
  | LAMBDA xs=arg+ COMMA t=term { make_pos $loc (P_Abst(xs, t)) }
  | LET x=ID a=arg* b=preceded(COLON, term)? ASSIGN t=term IN u=term
      {
        let x = make_pos $loc(x) (fst x) in
        make_pos $loc (P_LLet(x, a, b, t, u))
      }

rule:
  | l=term REWRITE r=term { make_pos $loc (l, r) }

%%
