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
%token FATARROW
%token LONGARROW
%token DEF
%token LEFTPAR
%token RIGHTPAR
%token LEFTSQU
%token RIGHTSQU
%token EVAL
%token INFER
%token <bool> ASSERT
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
  | KW_DEF s=ID COLON a=term DEF t=term DOT {
      make_pos $loc (P_definition(false, make_pos $loc(s) s, [], Some(a), t))
    }
  | KW_DEF s=ID DEF t=term DOT {
      make_pos $loc (P_definition(false, make_pos $loc(s) s, [], None, t))
    }
  | KW_DEF s=ID ps=param+ COLON a=term DEF t=term DOT {
      make_pos $loc (P_definition(false, make_pos $loc(s) s, ps, Some(a), t))
    }
  | KW_DEF s=ID ps=param+ DEF t=term DOT {
      make_pos $loc (P_definition(false, make_pos $loc(s) s, ps, None, t))
    }
  | KW_THM s=ID COLON a=term DEF t=term DOT {
      make_pos $loc (P_definition(true , make_pos $loc(s) s, [], Some(a), t))
    }
  | KW_THM s=ID ps=param+ COLON a=term DEF t=term DOT {
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
      make_pos $loc (P_require([r], P_require_default))
    }
  | EOF {
      raise End_of_file
    }

eval_config:
  | LEFTSQU s=ID RIGHTSQU {
      build_config s None
    }
  | LEFTSQU s1=ID COMMA s2=ID RIGHTSQU {
      build_config s1 (Some s2)
    }

param:
  | LEFTPAR id=ID COLON te=term RIGHTPAR {
      (make_pos $loc(id) id, Some(te))
    }

context_item:
  | x=ID ao=option(COLON a=term { a }) {
      (make_pos $loc(x) x, ao)
    }

rule:
  | LEFTSQU c=separated_list(COMMA, context_item) RIGHTSQU l=term LONGARROW r=term {
      make_pos $loc (c, l, r)
    }

sterm:
  | qid=QID    { make_pos $loc (P_Vari(make_pos $loc ([fst qid], snd qid))) }
  | id=ID      { make_pos $loc (P_Vari(make_pos $loc ([], id))) }
  | UNDERSCORE { make_pos $loc P_Wild }
  | TYPE       { make_pos $loc P_Type }
  | LEFTPAR t=term RIGHTPAR { t }

aterm:
  | t=aterm u=sterm { make_pos $loc (P_Appl(t,u)) }
  | t=sterm         { t }

term:
  | t=aterm { t }
  | x=ID COLON a=aterm ARROW b=term {
      make_pos $loc (P_Prod([(make_pos $loc(x) x, Some(a))], b))
    }
  | LEFTPAR x=ID COLON a=aterm RIGHTPAR ARROW b=term {
      make_pos $loc (P_Prod([(make_pos $loc(x) x, Some(a))], b))
    }
  | a=term ARROW b=term {
      make_pos $loc (P_Prod([(Pos.none "_", Some(a))], b))
    }
  | x=ID FATARROW t=term {
      make_pos $loc (P_Abst([(make_pos $loc(x) x, None)], t))
    }
  | x=ID COLON a=aterm FATARROW t=term {
      make_pos $loc (P_Abst([(make_pos $loc(x) x, Some(a))], t))
    }
%%
