%{
open Console
open Syntax
open Legacy_lexer

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
%token FARROW
%token LARROW
%token DEFEQ
%token L_PAR
%token R_PAR
%token L_SQB
%token R_SQB
%token EVAL
%token INFER
%token <bool> ASSERT
%token WILD
%token <string list> REQUIRE
%token TYPE
%token KW_DEF
%token KW_INJ
%token KW_THM
%token <string> ID
%token <string list * string> QID

%start line
%type <Syntax.p_cmd Pos.loc> line

%right ARROW FARROW

%%

line:
  | s=ID ps=param* COLON a=term DOT {
      let a = if ps = [] then a else make_pos $loc(a) (P_Prod(ps,a)) in
      make_pos $loc (P_symbol([Sym_const], make_pos $loc(s) s, a))
    }
  | KW_DEF s=ID COLON a=term DOT {
      make_pos $loc (P_symbol([], make_pos $loc(s) s, a))
    }
  | KW_INJ s=ID COLON a=term DOT {
      make_pos $loc (P_symbol([Sym_inj], make_pos $loc(s) s, a))
    }
  | KW_DEF s=ID COLON a=term DEFEQ t=term DOT {
      make_pos $loc (P_definition(false, make_pos $loc(s) s, [], Some(a), t))
    }
  | KW_DEF s=ID DEFEQ t=term DOT {
      make_pos $loc (P_definition(false, make_pos $loc(s) s, [], None, t))
    }
  | KW_DEF s=ID ps=param+ COLON a=term DEFEQ t=term DOT {
      make_pos $loc (P_definition(false, make_pos $loc(s) s, ps, Some(a), t))
    }
  | KW_DEF s=ID ps=param+ DEFEQ t=term DOT {
      make_pos $loc (P_definition(false, make_pos $loc(s) s, ps, None, t))
    }
  | KW_THM s=ID COLON a=term DEFEQ t=term DOT {
      make_pos $loc (P_definition(true , make_pos $loc(s) s, [], Some(a), t))
    }
  | KW_THM s=ID ps=param+ COLON a=term DEFEQ t=term DOT {
      make_pos $loc (P_definition(true , make_pos $loc(s) s, ps, Some(a), t))
    }
  | rs=rule+ DOT {
      make_pos $loc (P_rules(List.map translate_old_rule rs))
    }
  | EVAL t=term DOT {
      make_pos $loc (P_normalize(t, Eval.{strategy = SNF; steps = None}))
    }
  | EVAL c=eval_config t=term DOT {
      let c = Eval.(if c.strategy=NONE then {c with strategy=SNF} else c) in
      make_pos $loc (P_normalize(t, c))
    }
  | INFER t=term DOT {
      make_pos $loc (P_infer(t, Eval.{strategy = NONE; steps = None}))
    }
  | INFER c=eval_config t=term DOT {
      make_pos $loc (P_infer(t, c))
    }
  | mf=ASSERT t=aterm COLON a=term DOT {
      make_pos $loc (P_assert(mf, P_assert_typing(t,a)))
    }
  | mf=ASSERT t=aterm EQUAL u=term DOT {
      make_pos $loc (P_assert(mf, P_assert_conv(t,u)))
    }
  | r=REQUIRE    DOT {
      make_pos $loc (P_require(r, P_require_default))
    }
  | EOF {
      raise End_of_file
    }

eval_config:
  | L_SQB s=ID R_SQB              { build_config s None       }
  | L_SQB s1=ID COMMA s2=ID R_SQB { build_config s1 (Some s2) }

param:
  | L_PAR id=ID COLON te=term R_PAR { (make_pos $loc(id) id, Some(te)) }

context_item:
  | x=ID ao=option(COLON a=term { a }) { (make_pos $loc(x) x, ao) }

rule:
  | L_SQB c=separated_list(COMMA, context_item) R_SQB l=term LARROW r=term {
      make_pos $loc (c, l, r)
    }

sterm:
  | qid=QID            { make_pos $loc (P_Vari(make_pos $loc qid)) }
  | id=ID              { make_pos $loc (P_Vari(make_pos $loc ([], id))) }
  | WILD               { make_pos $loc P_Wild }
  | TYPE               { make_pos $loc P_Type }
  | L_PAR t=term R_PAR { t }

aterm:
  | t=aterm u=sterm { make_pos $loc (P_Appl(t,u)) }
  | t=sterm         { t }

term:
  | t=aterm { t }
  | x=ID COLON a=aterm ARROW b=term {
      make_pos $loc (P_Prod([(make_pos $loc(x) x, Some(a))], b))
    }
  | L_PAR x=ID COLON a=aterm R_PAR ARROW b=term {
      make_pos $loc (P_Prod([(make_pos $loc(x) x, Some(a))], b))
    }
  | a=term ARROW b=term {
      make_pos $loc (P_Prod([(Pos.none "_", Some(a))], b))
    }
  | x=ID FARROW t=term {
      make_pos $loc (P_Abst([(make_pos $loc(x) x, None)], t))
    }
  | x=ID COLON a=aterm FARROW t=term {
      make_pos $loc (P_Abst([(make_pos $loc(x) x, Some(a))], t))
    }
%%
