%{
    open Common.Pos
    open Syntax
    open DkBasic

    let wild loc = in_pos loc P_Wild

    let type_ loc = make_pos loc P_Type

    let p_ident (loc, s) = in_pos loc s

    let p_qident_of_id (loc, s) = in_pos loc ([], s)

    let p_qident_of_qid (loc, m, s) = in_pos loc ([m], s)

    let iden loc p_qid = in_pos loc (P_Iden (p_qid, false))

    let iden_of_id ((loc, _) as i) = iden loc (p_qident_of_id i)

    let iden_of_qid ((loc, _, _) as i) = iden loc (p_qident_of_qid i)

    let app t ts =
      List.fold_left (fun t ti -> make (cat t.pos ti.pos) (P_Appl(t,ti))) t ts

    let arrow loc t u = make_pos loc (P_Arro (t, u))

    let param (loc, s) = if s = "_" then None else Some (in_pos loc s)

    let params id topt = [param id], topt, false

    let abst loc id topt u = make_pos loc (P_Abst([params id topt], u))

    let prod loc id t u = make_pos loc (P_Prod([params id (Some t)], u))

    let let_ loc i t u v = make_pos loc (P_LLet(p_ident i, [], Some t, u, v))

    let opaq loc = in_pos loc P_opaq
    let protec loc = in_pos loc (P_expo Protec)
    let ac loc = in_pos loc (P_prop (AC false))
    let inj loc = in_pos loc (P_prop Injec)

    let symbol loc p_sym_mod i ps p_sym_typ p_sym_trm =
      make_pos loc (P_symbol
        { p_sym_mod
        ; p_sym_nam = p_ident i
        ; p_sym_arg = List.map (fun (i,t) -> params i (Some t)) ps
        ; p_sym_typ
        ; p_sym_trm
        ; p_sym_prf = None
        ; p_sym_def = match p_sym_trm with Some _ -> true | _ -> false })

(* parsing/menhir_parser.mly *)
%}

%token EOF
%token DOT
%token COMMA
%token COLON
%token EQUAL
%token ARROW
%token FATARROW
%token LONGARROW
%token DEF
%token LEFTPAR
%token RIGHTPAR
%token LEFTBRA
%token RIGHTBRA
%token LEFTSQU
%token RIGHTSQU
%token <Common.Pos.pos> EVAL
%token <Common.Pos.pos> INFER
%token <Common.Pos.pos> CHECK
%token <Common.Pos.pos> CHECKNOT
%token <Common.Pos.pos> ASSERT
%token <Common.Pos.pos> ASSERTNOT
%token <Common.Pos.pos> PRINT
%token <Common.Pos.pos> GDT
%token <Common.Pos.pos> UNDERSCORE
%token <Common.Pos.pos*DkBasic.mident> NAME
%token <Common.Pos.pos*DkBasic.mident> REQUIRE
%token <Common.Pos.pos> TYPE
%token <Common.Pos.pos> KW_DEF
%token <Common.Pos.pos> KW_DEFAC
%token <Common.Pos.pos> KW_DEFACU
%token <Common.Pos.pos> KW_THM
%token <Common.Pos.pos> KW_INJ
%token <Common.Pos.pos> KW_PRV
%token <Common.Pos.pos*DkBasic.ident> ID
%token <Common.Pos.pos*DkBasic.mident*DkBasic.ident> QID
%token <string> STRING

%start line
%type <Syntax.p_command> line

%%

line:
  | id=ID ps=param* COLON ty=term DOT
    { symbol $sloc [] id ps (Some ty) None }
  | KW_PRV id=ID ps=param* COLON ty=term DOT
    { symbol $sloc [protec $1] id ps (Some ty) None }
  | KW_DEF id=ID COLON ty=term DOT
    { symbol $sloc [] id [] (Some ty) None }
  | KW_PRV KW_DEF id=ID COLON ty=term DOT
    { symbol $sloc [protec $1] id [] (Some ty) None }
  | KW_INJ id=ID COLON ty=term DOT
    { symbol $sloc [inj $1] id [] (Some ty) None }
  | KW_PRV KW_INJ id=ID COLON ty=term DOT
    { symbol $sloc [protec $1; inj $2] id [] (Some ty) None }
  | KW_DEFAC id=ID LEFTSQU ty=term RIGHTSQU DOT
    { symbol $sloc [ac $1] id [] (Some ty) None }
  | KW_PRV KW_DEFAC id=ID LEFTSQU ty=term RIGHTSQU DOT
    { symbol $sloc [protec $1; ac $2] id [] (Some ty) None }
  | KW_DEFACU id=ID LEFTSQU ty=term COMMA neu=term RIGHTSQU DOT
    { symbol $sloc [ac $1] id [] (Some ty) None
      (*FIXME: neutral element ignored*) }
  | KW_PRV KW_DEFACU id=ID LEFTSQU ty=term COMMA neu=term RIGHTSQU DOT
    { symbol $sloc [protec $1; ac $2] id [] (Some ty) None
      (*FIXME: neutral element ignored*) }
  | KW_DEF id=ID COLON ty=term DEF te=term DOT
    { symbol $sloc [] id [] (Some ty) (Some te) }
  | KW_DEF id=ID DEF te=term DOT
    { symbol $sloc [] id [] None (Some te) }
  | KW_DEF id=ID ps=param+ COLON ty=term DEF te=term DOT
    { symbol $sloc [] id ps (Some ty) (Some te) }
  | KW_DEF id=ID ps=param+ DEF te=term DOT
    { symbol $sloc [] id ps None (Some te) }
  | KW_PRV KW_DEF id=ID COLON ty=term DEF te=term DOT
    { symbol $sloc [protec $1] id [] (Some ty) (Some te) }
  | KW_PRV KW_DEF id=ID DEF te=term DOT
    { symbol $sloc [protec $1] id [] None (Some te) }
  | KW_PRV KW_DEF id=ID ps=param+ COLON ty=term DEF te=term DOT
    { symbol $sloc [protec $1] id ps (Some ty) (Some te) }
  | KW_PRV KW_DEF id=ID ps=param+ DEF te=term DOT
    { symbol $sloc [protec $1] id ps None (Some te) }
  | KW_THM id=ID COLON ty=term DEF te=term DOT
    { symbol $sloc [opaq $1] id [] (Some ty) (Some te) }
  | KW_THM id=ID ps=param+ COLON ty=term DEF te=term DOT
    { symbol $sloc [opaq $1] id ps (Some ty) (Some te) }
  | rs=rule+ DOT
    { make_pos $sloc (P_rules (List.map DkRule.to_p_rule rs)) }

  | EVAL te=term DOT
      {fun md -> Eval($1, default_cfg, scope_term md [] te)}
  | EVAL cfg=eval_config te=term DOT
      {fun md -> Eval($1, cfg, scope_term md [] te)}
  | INFER te=term DOT
      {fun md -> Infer($1, default_cfg, scope_term md [] te)}
  | INFER cfg=eval_config te=term DOT
      {fun md -> Infer($1, cfg, scope_term md [] te)}

  | CHECK te=aterm COLON ty=term DOT
    { TODO }
  | CHECKNOT te=aterm COLON ty=term DOT
    { TODO }
  | ASSERT te=aterm COLON ty=term DOT
    { TODO }
  | ASSERTNOT te=aterm COLON ty=term DOT
    { TODO }

  | CHECK t1=aterm EQUAL t2=term DOT
    { TODO }
  | CHECKNOT t1=aterm EQUAL t2=term DOT
    { TODO }
  | ASSERT t1=aterm EQUAL t2=term DOT
    { TODO }
  | ASSERTNOT t1=aterm EQUAL t2=term DOT
    { TODO }

  | PRINT STRING DOT {fun _ -> Print($1, $2)}
  | GDT   ID     DOT {fun _ -> DTree($1, None, snd $2)}
  | GDT   QID    DOT {fun _ -> let (_,m,v) = $2 in DTree($1, Some m, v)}
  | n=NAME       DOT {fun _ -> Name(fst n, snd n)}
  | r=REQUIRE    DOT {fun _ -> Require(fst r,snd r)}
  | EOF              {raise End_of_file}

eval_config:
  | LEFTSQU l=separated_nonempty_list(COMMA, ID) RIGHTSQU
    { TODO }

param:
  | LEFTPAR id=ID COLON te=term RIGHTPAR
    { (id, te) }

rule:
  | LEFTSQU context RIGHTSQU top_pattern LONGARROW term
    { make_pos $sloc ($2, $4, $6) }
  | LEFTBRA ID RIGHTBRA LEFTSQU context RIGHTSQU top_pattern LONGARROW term
    { make_pos $sloc ($5, $7, $9) }
  | LEFTBRA QID RIGHTBRA LEFTSQU context RIGHTSQU top_pattern LONGARROW term
    { make_pos $sloc ($5, $7, $9) }

decl:
  | ID COLON term { ($1, Some $3) }
  | ID            { ($1, None   ) }

context: separated_list(COMMA, decl) { $1 }

top_pattern:
  | ID  pattern_wp* { app (iden_of_id $1) $2 }
  | QID pattern_wp* { app (iden_of_qid $1) $2 }

%inline pid:
  | UNDERSCORE { ($1, underscore) }
  | ID { $1 }

pattern_wp:
  | ID                       { iden_of_id $1 }
  | QID                      { iden_of_qid $1 }
  | UNDERSCORE               { wild $1 }
  | LEFTBRA term RIGHTBRA    { $2 }
  | LEFTPAR pattern RIGHTPAR { $2 }

pattern:
  | pid FATARROW pattern     { abst $sloc $1 None $3 }
  | ID  pattern_wp+          { app (iden_of_id $1) $2 }
  | QID pattern_wp+          { app (iden_of_qid $1) $2 }
  | UNDERSCORE pattern_wp+   { app (wild $1) $2 }
  | pattern_wp               { $1 }

sterm:
  | QID                      { iden_of_qid $1 }
  | ID                       { iden_of_id $1 }
  | LEFTPAR term RIGHTPAR    { $2 }
  | TYPE                     { type_ }

aterm:
  | te=sterm ts=sterm*
      {match ts with [] -> te | a::args -> PreApp(te,a,args)}

term:
  | t=aterm
      { t }
  | pid COLON aterm ARROW term
      { prod $sloc $1 $3 $5 }
  | LEFTPAR ID COLON aterm RIGHTPAR ARROW term
      { prod $sloc $2 $4 $7 }
  | aterm ARROW term
      { make_pos $sloc (P_Arro ($1, $3)) }
  | pid FATARROW term
      { abst $sloc $1 None $3 }
  | pid COLON aterm FATARROW term
      { abst $sloc $1 (Some $3) $5 }
  | LEFTPAR pid COLON aterm DEF aterm RIGHTPAR FATARROW term
      { let_ $sloc $2 $4 $6 $9 }
%%
