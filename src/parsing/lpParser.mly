(** Lambdapi parser, using the parser generator Menhir. *)

%{
  open Lplib
  open Common open Pos
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
%token CHANGE
%token COERCE_RULE
%token COMMUTATIVE
%token COMPUTE
%token CONSTANT
%token DEBUG
%token END
%token EVAL
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
%token ORELSE
%token POSTFIX
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
%token REMOVE
%token REPEAT
%token REQUIRE
%token REWRITE
%token RULE
%token SEARCH
%token SEQUENTIAL
%token SET
%token SIMPLIFY
%token SOLVE
%token SYMBOL
%token SYMMETRY
%token TRY
%token TYPE_QUERY
%token TYPE_TERM
%token UNIF_RULE
%token VERBOSE
%token WHY3
%token WITH

// other tokens

%token <bool * string> DEBUG_FLAGS
%token <string> INT
%token <string> FLOAT
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
%token <int> UID_META
%token <string> UID_PATT
%token <Path.t> QID
%token <Path.t> QID_EXPL

// types

%start <Syntax.p_command> command
%start <Syntax.p_qident> qid
%start <Syntax.p_qident> qid_alone
%start <Syntax.p_term> term_alone
%start <Syntax.p_rw_patt> rw_patt_spec_alone
%start <SearchQuerySyntax.query> search_query_alone

// patch (see https://github.com/Deducteam/lambdapi/pull/798)
%type <Syntax.p_term * Syntax.p_term> equation

%%

term_alone:
  | t=term EOF
    { t }

rw_patt_spec_alone:
  | p=rw_patt_spec EOF
    { p }

qid_alone:
  | q=qid EOF
    { q }

search_query_alone:
  | q=search_query EOF
    { q }

command:
  | OPAQUE i=qid SEMICOLON { make_pos $sloc (P_opaque i) }
  | REQUIRE l=list(path) SEMICOLON
    { make_pos $sloc (P_require(None,l)) }
  | REQUIRE b=open_cmd l=list(path) SEMICOLON
    { make_pos $sloc (P_require(Some b,l)) }
  | REQUIRE p=path AS i=uid SEMICOLON
    { make_pos $sloc (P_require_as(p,i)) }
  | b=open_cmd l=list(path) SEMICOLON
    { make_pos $sloc (P_open(b,l)) }
  | ms=modifier* SYMBOL s=uid al=param_list* COLON a=term
    po=proof? SEMICOLON
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
  | exp=exposition? xs=param_list* INDUCTIVE
    is=separated_nonempty_list(WITH, inductive) SEMICOLON
      { make_pos $sloc (P_inductive(Option.to_list exp,xs,is)) }
  | RULE rs=separated_nonempty_list(WITH, rule) SEMICOLON
      { make_pos $sloc (P_rules(rs)) }
  | BUILTIN s=STRINGLIT ASSIGN i=qid SEMICOLON
    { make_pos $loc (P_builtin(s,i)) }
  | COERCE_RULE r=rule SEMICOLON { make_pos $loc (P_coercion r) }
  | UNIF_RULE r=unif_rule SEMICOLON { make_pos $loc (P_unif_rule(r)) }
  | NOTATION i=qid n=notation SEMICOLON
    { make_pos $loc (P_notation(i,n)) }
  | q=query SEMICOLON { make_pos $sloc (P_query(q)) }
  | EOF { raise End_of_file }

open_cmd:
  | OPEN { false }
  | PRIVATE OPEN { true }

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
  | PRINT i=qid_or_rule? { make_pos $sloc (P_query_print i) }
  | PROOFTERM { make_pos $sloc P_query_proofterm }
  | DEBUG { make_pos $sloc (P_query_debug(true,"")) }
  | DEBUG fl=DEBUG_FLAGS
    { let (b, s) = fl in make_pos $sloc (P_query_debug(b, s)) }
  | FLAG { make_pos $sloc (P_query_flag("",true)) }
  | FLAG s=STRINGLIT b=SWITCH { make_pos $sloc (P_query_flag(s,b)) }
  | PROVER s=STRINGLIT { make_pos $sloc (P_query_prover(s)) }
  | PROVER_TIMEOUT n=INT
    { make_pos $sloc (P_query_prover_timeout n) }
  | VERBOSE n=INT { make_pos $sloc (P_query_verbose n) }
  | TYPE_QUERY t=term
    { make_pos $sloc (P_query_infer(t, {strategy=NONE; steps=None}))}
  | SEARCH s=STRINGLIT
    { make_pos $sloc (P_query_search s) }

qid_or_rule:
  | i=qid { i }
  | UNIF_RULE
    { make_pos $sloc (Sign.Ghost.path, Unif_rule.equiv.sym_name) }
  | COERCE_RULE
    { make_pos $sloc (Sign.Ghost.path, Coercion.coerce.sym_name) }

path:
  | UID { LpLexer.syntax_error $sloc "Unqualified identifier" }
  | p=QID { make_pos $sloc (List.rev p) }

modifier:
  | d=ioption(SIDE) ASSOCIATIVE
    { let b = match d with Some Pratter.Left -> true | _ -> false in
      make_pos $sloc (P_prop (Term.Assoc b)) }
  | COMMUTATIVE { make_pos $sloc (P_prop Term.Commu) }
  | CONSTANT { make_pos $sloc (P_prop Term.Const) }
  | INJECTIVE { make_pos $sloc (P_prop Term.Injec) }
  | OPAQUE { make_pos $sloc P_opaq }
  | SEQUENTIAL { make_pos $sloc (P_mstrat Term.Sequen) }
  | exp=exposition { exp }

exposition:
| PRIVATE { make_pos $sloc (P_expo Term.Privat) }
| PROTECTED { make_pos $sloc (P_expo Term.Protec) }

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
  | s=UID_META ts=env?
    { let i = make_pos $loc(s) s
      and ts = match ts with None -> [||] | Some ts -> Array.of_list ts in
      make_pos $sloc (P_Meta(i,ts)) }
  | s=UID_PATT e=env?
    { let i = if s = "_" then None else Some(make_pos $loc(s) s) in
      make_pos $sloc (P_Patt(i, Option.map Array.of_list e)) }
  | L_PAREN t=term R_PAREN { make_pos $sloc (P_Wrap(t)) }
  | L_SQ_BRACKET t=term R_SQ_BRACKET { make_pos $sloc (P_Expl(t)) }
  | n=INT { make_pos $sloc (P_NLit n) }
  | s=STRINGLIT { make_pos $sloc (P_SLit s) }

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
  | CHANGE t=term { make_pos $sloc (P_tac_change t) }
  | EVAL t=term { make_pos $sloc (P_tac_eval t) }
  | FAIL { make_pos $sloc P_tac_fail }
  | GENERALIZE i=uid { make_pos $sloc (P_tac_generalize i) }
  | HAVE i=uid COLON t=term { make_pos $sloc (P_tac_have(i,t)) }
  | INDUCTION { make_pos $sloc P_tac_induction }
  | ORELSE t1=tactic t2=tactic { make_pos $sloc (P_tac_orelse(t1,t2)) }
  | REFINE t=term { make_pos $sloc (P_tac_refine t) }
  | REFLEXIVITY { make_pos $sloc P_tac_refl }
  | REMOVE xs=uid+ { make_pos $sloc (P_tac_remove xs) }
  | REPEAT t=tactic { make_pos $sloc (P_tac_repeat t) }
  | REWRITE d=SIDE? p=rw_patt_spec? t=term
    { let b = match d with Some Pratter.Left -> false | _ -> true in
      make_pos $sloc (P_tac_rewrite(b,p,t)) }
  | SET i=uid ASSIGN t=term { make_pos $sloc (P_tac_set(i,t)) }
  | SIMPLIFY { make_pos $sloc (P_tac_simpl SimpAll) }
  | SIMPLIFY i=qid { make_pos $sloc (P_tac_simpl (SimpSym i)) }
  | SIMPLIFY RULE s=SWITCH
    { if s then LpLexer.syntax_error $sloc "Invalid tactic"
      else make_pos $sloc (P_tac_simpl SimpBetaOnly) }
  | SOLVE { make_pos $sloc P_tac_solve }
  | SYMMETRY { make_pos $sloc P_tac_sym }
  | TRY t=tactic { make_pos $sloc (P_tac_try t) }
  | WHY3 s=STRINGLIT? { make_pos $sloc (P_tac_why3 s) }

rw_patt:
  | t=term { make_pos $sloc (Rw_Term(t)) }
  | IN t=term { make_pos $sloc (Rw_InTerm(t)) }
  | IN x=uid IN t=term { make_pos $sloc (Rw_InIdInTerm(x, t)) }
  | u=term IN x=term t=preceded(IN, term)?
    { let ident_of_term {elt; _} =
        match elt with
        | P_Iden({elt=([], x); pos}, _) -> Pos.make pos x
        | _ -> LpLexer.syntax_error $sloc "Not an identifier"
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
      let equiv = P.qiden Sign.Ghost.path Unif_rule.equiv.sym_name in
      let cons = P.qiden Sign.Ghost.path Unif_rule.cons.sym_name in
      let mk_equiv (t, u) = P.appl (P.appl equiv t) u in
      let lhs = mk_equiv e in
      let es = List.rev_map mk_equiv es in
      let (en, es) = List.(hd es, tl es) in
      let cat e es = P.appl (P.appl cons e) es in
      let rhs = List.fold_right cat es en in
      make_pos $sloc (lhs, rhs) }

equation: l=term EQUIV r=term { (l, r) }

notation:
  | INFIX a=SIDE? p=float_or_int
    { Term.Infix(Option.get Pratter.Neither a, p) }
  | POSTFIX p=float_or_int { Term.Postfix(p) }
  | PREFIX p=float_or_int { Term.Prefix(p) }
  | QUANTIFIER { Term.Quant }

float_or_int:
  | s=FLOAT { s }
  | s=INT { s }

maybe_generalize:
  | g = GENERALIZE?
    { g <> None }

where:
  | u = UID g=maybe_generalize
    { g, match u with
       | "=" -> Some SearchQuerySyntax.Exact
       | ">" -> Some SearchQuerySyntax.Inside
       | "≥"
       | ">=" -> None
       | _ ->
          LpLexer.syntax_error $sloc
           "Only \">\", \"=\", \"≥\" and \">=\" accepted"
    }

asearch_query:
  (* "type" is a keyword... *)
  | TYPE_QUERY gw=where t=aterm
    { let g,w = gw in
      if w <> None then
        LpLexer.syntax_error $sloc
         "Only \"≥\" and \">=\" accepted for \"type\""
      else
       SearchQuerySyntax.QBase(QSearch(t,g,Some (QType None))) }
  | RULE gw=where t=aterm
    { let g,w = gw in
      SearchQuerySyntax.QBase(QSearch(t,g,Some (QXhs(w,None)))) }
  | k=UID gw=where t=aterm
    { let open SearchQuerySyntax in
      let g,w = gw in
      match k,t.elt with
       | "name",P_Iden(id,false) ->
           assert (fst id.elt = []) ;
           if w <> Some Exact then
             LpLexer.syntax_error $sloc
              "Only \"=\" accepted for \"name\""
           else if g = true then
             LpLexer.syntax_error $sloc
              "\"generalize\" cannot be used with \"name\""
           else
             QBase(QName (snd id.elt))
       | "name",_ ->
           LpLexer.syntax_error $sloc "Path prefix expected after \"name:\""
       | "anywhere",_ ->
           if w <> None then
             LpLexer.syntax_error $sloc
              "Only \"≥\" and \">=\" accepted for \"anywhere\""
           else
             QBase(QSearch(t,g,None))
       | "spine",_ ->
           QBase(QSearch(t,g,Some (QType (Some (Spine w)))))
       | "concl",_ ->
           QBase(QSearch(t,g,Some (QType (Some (Conclusion w)))))
       | "hyp",_ ->
           QBase(QSearch(t,g,Some (QType (Some (Hypothesis w)))))
       | "lhs",_ ->
           QBase(QSearch(t,g,Some (QXhs(w,Some Lhs))))
       | "rhs",_ ->
           QBase(QSearch(t,g,Some (QXhs(w,Some Rhs))))
       | _,_ ->
           LpLexer.syntax_error $sloc ("Unknown keyword: " ^ k)
    }
  | L_PAREN q=search_query R_PAREN
    { q }

csearch_query:
  | q=asearch_query
    { q }
  | q1=csearch_query COMMA q2=asearch_query
    { SearchQuerySyntax.QOpp (q1,SearchQuerySyntax.Intersect,q2) }

ssearch_query:
  | q=csearch_query
    { q }
  | q1=ssearch_query SEMICOLON q2=csearch_query
    { SearchQuerySyntax.QOpp (q1,SearchQuerySyntax.Union,q2) }

search_query:
  | q=ssearch_query
    { q }
  | q=search_query VBAR qid=qid
    { let p,n = qid.elt in
      let path =
       if p = [] then n
       else
        Format.asprintf "%a.%a" Core.Print.path p Core.Print.uid n in
      SearchQuerySyntax.QFilter (q,Path path) }

%%
