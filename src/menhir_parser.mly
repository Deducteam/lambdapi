%{
open Console
open Syntax

let build_config : string -> string option -> Eval.config = fun s1 s2o ->
  try
    let open Eval in
    let config steps strategy =
      let steps =
        match steps with
        | None     -> None
        | Some(nb) -> Some(int_of_string nb)
      in
      {strategy; steps}
    in
    match (s1, s2o) with
    | ("SNF" , io         ) -> config io        SNF
    | ("HNF" , io         ) -> config io        HNF
    | ("WHNF", io         ) -> config io        WHNF
    | (i     , Some "SNF" ) -> config (Some(i)) SNF
    | (i     , Some "HNF" ) -> config (Some(i)) HNF
    | (i     , Some "WHNF") -> config (Some(i)) WHNF
    | (i     , None       ) -> config (Some(i)) NONE
    | (_     , _          ) -> raise Exit (* captured below *)
  with _ -> fatal_no_pos "Invalid command configuration."
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
%token LEFTSQU
%token RIGHTSQU
%token EVAL
%token INFER
%token ASSERT
%token ASSERTNOT
%token UNDERSCORE
%token <string> REQUIRE
%token TYPE
%token KW_DEF
%token KW_INJ
%token KW_THM
%token <string> ID
%token <string*string> QID

%start line
%type <Syntax.p_cmd Pos.loc> line

%right ARROW FATARROW

%%

line:
  | s=ID COLON a=term DOT
      { Pos.none (P_symbol([Sym_const], Pos.none s, a)) }
  | s=ID ps=param+ COLON a=term DOT
      { Pos.none (P_symbol([Sym_const],Pos.none s,Pos.none (P_Prod(ps,a)))) }
  | KW_DEF s=ID COLON a=term DOT
      { Pos.none (P_symbol([], Pos.none s, a)) }
  | KW_INJ s=ID COLON a=term DOT
      { Pos.none (P_symbol([Sym_inj], Pos.none s, a)) }
  | KW_DEF s=ID COLON a=term DEF t=term DOT
      { Pos.none (P_definition(false, Pos.none s, [], Some(a), t)) }
  | KW_DEF s=ID DEF t=term DOT
      { Pos.none (P_definition(false, Pos.none s, [], None, t)) }
  | KW_DEF s=ID ps=param+ COLON a=term DEF t=term DOT
      { Pos.none (P_definition(false, Pos.none s, ps, Some(a), t)) }
  | KW_DEF s=ID ps=param+ DEF t=term DOT
      { Pos.none (P_definition(false, Pos.none s, ps, None, t)) }
  | KW_THM s=ID COLON a=term DEF t=term DOT
      { Pos.none (P_definition(true , Pos.none s, [], Some(a), t)) }
  | KW_THM s=ID ps=param+ COLON a=term DEF t=term DOT
      { Pos.none (P_definition(true , Pos.none s, ps, Some(a), t)) }
  | rs=rule+ DOT
      { Pos.none (P_rules(List.map translate_old_rule rs)) }
  | EVAL t=term DOT
      { Pos.none (P_normalize(t, Eval.{strategy = SNF; steps = None})) }
  | EVAL c=eval_config t=term DOT
      { let c = Eval.(if c.strategy=NONE then {c with strategy=SNF} else c) in
        Pos.none (P_normalize(t, c)) }
  | INFER t=term DOT
      { Pos.none (P_infer(t, Eval.{strategy = NONE; steps = None})) }
  | INFER c=eval_config t=term DOT
      { Pos.none (P_infer(t, c)) }
  | ASSERT    t=aterm COLON a=term DOT
      { Pos.none (P_assert(false, P_assert_typing(t,a))) }
  | ASSERTNOT t=aterm COLON a=term DOT
      { Pos.none (P_assert(true , P_assert_typing(t,a))) }
  | ASSERT    t=aterm EQUAL u=term DOT
      { Pos.none (P_assert(false, P_assert_conv(t,u))) }
  | ASSERTNOT t=aterm EQUAL u=term DOT
      { Pos.none (P_assert(true , P_assert_conv(t,u))) }
  | r=REQUIRE    DOT { Pos.none (P_require([r], P_require_default)) }
  | EOF              { raise End_of_file }

eval_config:
  | LEFTSQU s=ID RIGHTSQU              { build_config s None }
  | LEFTSQU s1=ID COMMA s2=ID RIGHTSQU { build_config s1 (Some s2) }

param:
  | LEFTPAR id=ID COLON te=term RIGHTPAR { (Pos.none id, Some(te)) }

rule:
  | LEFTSQU c=context RIGHTSQU lhs=term LONGARROW rhs=term
      { Pos.none (c, lhs, rhs ) }

context_item:
  | x=ID ao=option(COLON a=term { a }) { (Pos.none x, ao) }

context:
  | l=separated_list(COMMA, context_item) { l }

sterm:
  | qid=QID
      { let (m,id)=qid in Pos.none (P_Vari(Pos.none([m], id))) }
  | id=ID
      { Pos.none (P_Vari(Pos.none([], id))) }
  | LEFTPAR t=term RIGHTPAR
      { t }
  | UNDERSCORE
      { Pos.none P_Wild }
  | TYPE
      { Pos.none P_Type }

aterm:
  | t=sterm ts=sterm*
      { List.fold_left (fun t u -> Pos.none (P_Appl(t,u))) t ts }

term:
  | t=aterm
      { t }
  | x=ID COLON a=aterm ARROW b=term
      { Pos.none (P_Prod([(Pos.none x, Some(a))], b)) }
  | LEFTPAR x=ID COLON a=aterm RIGHTPAR ARROW b=term
      { Pos.none (P_Prod([(Pos.none x, Some(a))], b)) }
  | a=term ARROW b=term
      { Pos.none (P_Prod([(Pos.none "_", Some(a))], b)) }
  | x=ID FATARROW t=term
      { Pos.none (P_Abst([(Pos.none x, None)], t)) }
  | x=ID COLON a=aterm FATARROW t=term
      { Pos.none (P_Abst([(Pos.none x, Some(a))], t)) }
%%
