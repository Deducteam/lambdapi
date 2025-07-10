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

  exception Error
%}


// end of file

%token EOF

// keywords in alphabetical order

%token GENERALIZE
%token IN
%token LET
%token RULE
%token TYPE_QUERY
%token TYPE_TERM

// other tokens

%token <string> INT
%token <string> STRINGLIT

// symbols

%token ARROW
%token ASSIGN
%token BACKQUOTE
%token COMMA
%token COLON
%token DOT
%token EXISTS
%token FORALL
%token FUN
%token LAMBDA
%token L_PAREN
%token L_SQ_BRACKET
%token PI
%token R_PAREN
%token R_SQ_BRACKET
%token SEMICOLON
%token THICKARROW
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

%start <SearchQuerySyntax.query> search_query_alone

%%

search_query_alone:
  | q=search_query EOF
    { q }

uid: s=UID { make_pos $sloc s}

param_list:
  | x=param { ([x], None, false) }
  | L_PAREN xs=param+ COLON a=term R_PAREN { (xs, Some(a), false) }
  | L_SQ_BRACKET xs=param+ a=preceded(COLON, term)? R_SQ_BRACKET
    { (xs, a, true) }

fun_param_list:
  | x=param { ([x], None, false) }
  | L_PAREN xs=param+ COLON a=term R_PAREN { (xs, Some(a), false) }

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
  | EXISTS b=rocqbinder(COMMA)
     { {(List.fold_right
          (fun bin res ->
            Pos.none (P_Appl(
              Pos.none (P_Iden(Pos.none ([],"∃"), false)),
              Pos.none (P_Abst([bin], res)))))
          (fst b)
          (snd b))
         with pos = Some (Pos.locate $sloc) }
     } (* in Coq *)
  | FORALL b=rocqbinder(COMMA)
    { make_pos $sloc (P_Prod(fst b, snd b)) } (* in Coq *)
  | PI b=binder
    { make_pos $sloc (P_Prod(fst b, snd b)) } (* not in Coq! *)
  | LAMBDA b=binder
    { make_pos $sloc (P_Abst(fst b, snd b)) } (* not in Coq! *)
  | FUN b=rocqbinder(THICKARROW)
    { make_pos $sloc (P_Abst(fst b, snd b)) } (* in Coq *)
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

rocqbinder(terminator):
  | ps=fun_param_list+ a=preceded(COLON, term)? terminator t=term
    { if a = None then
       (ps, t)
      else if List.for_all (fun (_,typ,_) -> typ = None) ps then
       (List.map (fun (v,_,b) -> v,a,b) ps, t)
      else
       raise Error
    }

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
  | q=search_query VBAR s=STRINGLIT
    { let re = Str.regexp s in
      SearchQuerySyntax.QFilter (q,RegExp re) }

%%
