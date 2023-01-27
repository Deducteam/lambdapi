%{
    (** Modified version of the Dedukti source file
       parsing/menhir_parser.mly. *)

    open Common.Pos
    open Syntax
    open DkBasic
    open Common.Error

    let fail lps s = fatal (Some (locate lps)) s

    let wild lps = make_pos lps P_Wild

    let type_ lps = make_pos lps P_Type

    let p_ident (lps, s) = make_pos lps s

    let p_qident_of_id (lps, s) = make_pos lps ([], s)

    let p_qident_of_qid (lps, m, s) = make_pos lps ([m], s)

    let iden lps p_qid = make_pos lps (P_Iden (p_qid, false))

    let iden_of_id ((lps, _) as i) = iden lps (p_qident_of_id i)

    let iden_of_qid ((lps, _, _) as i) = iden lps (p_qident_of_qid i)

    let app t ts =
      List.fold_left (fun t ti -> make (cat t.pos ti.pos) (P_Appl(t,ti))) t ts

    let param (lps, s) = if s = "_" then None else Some (make_pos lps s)

    let params id topt = [param id], topt, false

    let abst lps id topt u = make_pos lps (P_Abst([params id topt], u))

    let prod lps id t u = make_pos lps (P_Prod([params id (Some t)], u))

    let let_ lps i t u v = make_pos lps (P_LLet(p_ident i, [], Some t, u, v))

    let defin lps = make_pos lps (P_prop Defin)
    let const lps = make_pos lps (P_prop Const)
    let inj lps = make_pos lps (P_prop Injec)
    let ac lps = make_pos lps (P_prop (AC false))

    let opaq lps = make_pos lps P_opaq
    let protec lps = make_pos lps (P_expo Protec)

    let symbol lps p_sym_mod i ps p_sym_typ p_sym_trm =
      make_pos lps (P_symbol
        { p_sym_mod
        ; p_sym_nam = p_ident i
        ; p_sym_arg = List.map (fun (i,t) -> params i (Some t)) ps
        ; p_sym_typ
        ; p_sym_trm
        ; p_sym_prf = None
        ; p_sym_def = match p_sym_trm with Some _ -> true | _ -> false })

    let strat =
      let open Core.Eval in
      function
      | [] | [_,"SNF"] -> {strategy=SNF; steps=None}
      | [_,"WHNF"] -> {strategy=WHNF; steps=None}
      | [(lps,_);(_,"SNF")]
      | [(lps,_);(_,"WHNF")]
      | [(_,"SNF");(lps,_)]
      | [(_,"WHNF");(lps,_)] -> fail lps "Command not supported"
      | (lps,_)::_ -> fail lps "Invalid strategy"

    let normalize lps t ids = make_pos lps (P_query_normalize(t, strat ids))
    let infer lps t ids = make_pos lps (P_query_infer(t, strat ids))

    let typing te ty = P_assert_typing (te, ty)
    let conv t1 t2 = P_assert_conv (t1, t2)

    let assertion lps b a = make_pos lps (P_query_assert(b,a))

    let query lps q = make_pos lps (P_query q)

    let require (lps,id) = make_pos lps (P_require(false,[make_pos lps [id]]))

    let type_class (lps,id) = make_pos lps (P_type_class (make_pos lps id))
    let type_class_instance (lps,id) = make_pos lps (P_type_class_instance (make_pos lps id))

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
%token <DkTokens.loc> EVAL
%token <DkTokens.loc> INFER
%token <DkTokens.loc> CHECK
%token <DkTokens.loc> CHECKNOT
%token <DkTokens.loc> ASSERT
%token <DkTokens.loc> ASSERTNOT
%token <DkTokens.loc> PRINT
%token <DkTokens.loc> GDT
%token <DkTokens.loc> UNDERSCORE
%token <DkTokens.loc*DkBasic.mident> NAME
%token <DkTokens.loc*DkBasic.mident> REQUIRE
%token <DkTokens.loc*DkBasic.mident> TYPE_CLASS
%token <DkTokens.loc*DkBasic.mident> TYPE_CLASS_INSTANCE
%token <DkTokens.loc> TYPE
%token <DkTokens.loc> KW_DEF
%token <DkTokens.loc> KW_DEFAC
%token <DkTokens.loc> KW_DEFACU
%token <DkTokens.loc> KW_THM
%token <DkTokens.loc> KW_INJ
%token <DkTokens.loc> KW_PRV
%token <DkTokens.loc*DkBasic.ident> ID
%token <DkTokens.loc*DkBasic.mident*DkBasic.ident> QID
%token <string> STRING

%start line
%type <Syntax.p_command> line

%%

line:
  | id=ID ps=param* COLON ty=term DOT
    { symbol $sloc [const(fst id)] id ps (Some ty) None }
  | KW_PRV id=ID ps=param* COLON ty=term DOT
    { symbol $sloc [const(fst id);protec $1] id ps (Some ty) None }
  | KW_DEF id=ID COLON ty=term DOT
    { symbol $sloc [defin $1] id [] (Some ty) None }
  | KW_PRV KW_DEF id=ID COLON ty=term DOT
    { symbol $sloc [protec $1; defin $2] id [] (Some ty) None }
  | KW_INJ id=ID COLON ty=term DOT
    { symbol $sloc [inj $1] id [] (Some ty) None }
  | KW_PRV KW_INJ id=ID COLON ty=term DOT
    { symbol $sloc [protec $1; inj $2] id [] (Some ty) None }
  | KW_DEFAC id=ID LEFTSQU ty=term RIGHTSQU DOT
    { symbol $sloc [ac $1] id [] (Some ty) None }
  | KW_PRV KW_DEFAC id=ID LEFTSQU ty=term RIGHTSQU DOT
    { symbol $sloc [protec $1; ac $2] id [] (Some ty) None }
  | KW_DEFACU id=ID LEFTSQU ty=term COMMA neu=term RIGHTSQU DOT
    { let _ = id and _ = ty and _ = neu in fail $1 "Unsupported command" }
  | KW_PRV KW_DEFACU id=ID LEFTSQU ty=term COMMA neu=term RIGHTSQU DOT
    { let _ = id and _ = ty and _ = neu in fail $2 "Unsupported command" }
  | KW_DEF id=ID COLON ty=term DEF te=term DOT
    { symbol $sloc [defin $1] id [] (Some ty) (Some te) }
  | KW_DEF id=ID DEF te=term DOT
    { symbol $sloc [defin $1] id [] None (Some te) }
  | KW_DEF id=ID ps=param+ COLON ty=term DEF te=term DOT
    { symbol $sloc [defin $1] id ps (Some ty) (Some te) }
  | KW_DEF id=ID ps=param+ DEF te=term DOT
    { symbol $sloc [defin $1] id ps None (Some te) }
  | KW_PRV KW_DEF id=ID COLON ty=term DEF te=term DOT
    { symbol $sloc [protec $1; defin $2] id [] (Some ty) (Some te) }
  | KW_PRV KW_DEF id=ID DEF te=term DOT
    { symbol $sloc [protec $1; defin $2] id [] None (Some te) }
  | KW_PRV KW_DEF id=ID ps=param+ COLON ty=term DEF te=term DOT
    { symbol $sloc [protec $1; defin $2] id ps (Some ty) (Some te) }
  | KW_PRV KW_DEF id=ID ps=param+ DEF te=term DOT
    { symbol $sloc [protec $1; defin $2] id ps None (Some te) }
  | KW_THM id=ID COLON ty=term DEF te=term DOT
    { symbol $sloc [opaq $1; defin(fst id)] id [] (Some ty) (Some te) }
  | KW_THM id=ID ps=param+ COLON ty=term DEF te=term DOT
    { symbol $sloc [opaq $1; defin(fst id)] id ps (Some ty) (Some te) }
  | rs=rule+ DOT
    { make_pos $sloc (P_rules (List.map DkRule.to_p_rule rs)) }

  | EVAL te=term DOT
    { query $sloc (normalize $sloc te []) }
  | EVAL cfg=eval_config te=term DOT
    { query $sloc (normalize $sloc te cfg) }
  | INFER te=term DOT
    { query $sloc (infer $sloc te []) }
  | INFER cfg=eval_config te=term DOT
    { query $sloc (infer $sloc te cfg) }

  | CHECK te=aterm COLON ty=term DOT
    { query $sloc (assertion $sloc false (typing te ty)) }
  | CHECKNOT te=aterm COLON ty=term DOT
    { query $sloc (assertion $sloc true (typing te ty)) }
  | ASSERT te=aterm COLON ty=term DOT
    { query $sloc (assertion $sloc false (typing te ty)) }
  | ASSERTNOT te=aterm COLON ty=term DOT
    { query $sloc (assertion $sloc true (typing te ty)) }

  | CHECK t1=aterm EQUAL t2=term DOT
    { query $sloc (assertion $sloc false (conv t1 t2)) }
  | CHECKNOT t1=aterm EQUAL t2=term DOT
    { query $sloc (assertion $sloc true (conv t1 t2)) }
  | ASSERT t1=aterm EQUAL t2=term DOT
    { query $sloc (assertion $sloc false (conv t1 t2)) }
  | ASSERTNOT t1=aterm EQUAL t2=term DOT
    { query $sloc (assertion $sloc true (conv t1 t2)) }

  | PRINT STRING DOT { fail $1 "Unsupported command" }
  | GDT   ID     DOT { fail $1 "Unsupported command" }
  | GDT   QID    DOT { fail $1 "Unsupported command" }
  | n=NAME       DOT { fail (fst n) "Unsupported command" }
  | r=REQUIRE    DOT { require r }
  | tc=TYPE_CLASS DOT { type_class tc }
  | tci=TYPE_CLASS_INSTANCE DOT { type_class_instance tci }
  | EOF              {raise End_of_file}

eval_config:
  | LEFTSQU l=separated_nonempty_list(COMMA, ID) RIGHTSQU
    { l }

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
  | ID COLON term { (p_ident $1, Some $3) }
  | ID            { (p_ident $1, None   ) }

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
  | TYPE                     { type_ $sloc }

aterm:
  | te=sterm ts=sterm*
    { app te ts }

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
