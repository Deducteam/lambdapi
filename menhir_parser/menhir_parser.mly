%{
open Raw

let build_prod : (string * p_term) list -> p_term -> p_term =
  List.fold_right (fun (x,a) b -> P_Prod(x, Some(a), b))

let build_abst : (string * p_term) list -> p_term -> p_term =
  List.fold_right (fun (x,a) b -> P_Abst(x, Some(a), b))

let build_config1 : string -> Eval.config = fun s ->
  assert false (* TODO *)

let build_config2 : string -> string -> Eval.config = fun s1 s2 ->
  assert false (* TODO *)
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
%token CHECK
%token CHECKNOT
%token ASSERT
%token ASSERTNOT
%token UNDERSCORE
%token <string> NAME
%token <string> REQUIRE
%token TYPE
%token KW_DEF
%token KW_THM
%token <string> ID
%token <string*string> QID

%start line
%type <Raw.p_cmd> line
%type <Raw.old_p_rule> rule
%type <string * Raw.p_term> param
%type <(string * Raw.p_term option) list> context
%type <Raw.p_term> sterm
%type <Raw.p_term> term
%type <Raw.Eval.config> eval_config

%right ARROW FATARROW

%%

line:
  | s=ID ps=param* COLON a=term DOT
      { P_SymDecl(true, s, build_prod ps a) }
  | KW_DEF s=ID COLON a=term DOT
      { P_SymDecl(false, s, a) }
  | KW_DEF s=ID COLON a=term DEF t=term DOT
      { P_SymDef(false, s, Some(a), t) }
  | KW_DEF s=ID DEF t=term DOT
      { P_SymDef(false, s,  None, t) }
  | KW_DEF s=ID ps=param+ COLON a=term DEF t=term DOT
      { P_SymDef(false, s, Some(build_prod ps a), build_abst ps t) }
  | KW_DEF s=ID ps=param+ DEF t=term DOT
      { P_SymDef(false, s, None, build_abst ps t) }
  | KW_THM s=ID COLON a=term DEF t=term DOT
      { P_SymDef(true, s, Some(a), t) }
  | KW_THM s=ID ps=param+ COLON a=term DEF t=term DOT
      { P_SymDef(true, s, Some(build_prod ps a), build_abst ps t) }
  | rs=rule+ DOT
      { P_OldRules(rs) }

  | EVAL t=term DOT
      { P_Eval(t, Eval.{strategy = SNF; steps = None}) }
  | EVAL c=eval_config t=term DOT
      { P_Eval(t, c) }
  | INFER t=term DOT
      { P_Infer(t, Eval.{strategy = SNF; steps = None}) }
  | INFER c=eval_config t=term DOT
      { P_Infer(t, c) }
  | CHECK     t=aterm COLON a=term DOT
      { P_TestType(false, false, t, a) }
  | CHECKNOT  t=aterm COLON a=term DOT
      { P_TestType(false, true , t, a) }
  | ASSERT    t=aterm COLON a=term DOT
      { P_TestType(true , false, t, a) }
  | ASSERTNOT t=aterm COLON a=term DOT
      { P_TestType(true , true , t, a) }

  | CHECK     t=aterm EQUAL u=term DOT
      { P_TestConv(false, false, t, u) }
  | CHECKNOT  t=aterm EQUAL u=term DOT
      { P_TestConv(false, true , t, u) }
  | ASSERT    t=aterm EQUAL u=term DOT
      { P_TestConv(true , false, t, u) }
  | ASSERTNOT t=aterm EQUAL u=term DOT
      { P_TestConv(true , true , t, u) }

  | NAME         DOT { P_Other("NAME") }
  | r=REQUIRE    DOT { P_Require([r]) }
  | EOF              { raise End_of_file }

eval_config:
  | LEFTSQU s=ID RIGHTSQU              { build_config1 s }
  | LEFTSQU s1=ID COMMA s2=ID RIGHTSQU { build_config2 s1 s2 }

param:
  | LEFTPAR id=ID COLON te=term RIGHTPAR { (id, te) }

rule:
  | LEFTSQU c=context RIGHTSQU lhs=term LONGARROW rhs=term { (c, lhs, rhs ) }

context:
  | l=separated_list(COMMA, ID) { List.map (fun x -> (x, None)) l }

%inline pid:
  | UNDERSCORE { "_" }
  | id=ID      { id }

sterm:
  | QID
      { let (m,id)=$1 in P_Vari([m],id) }
  | id=pid
      { P_Vari([], id) }
  | LEFTPAR t=term RIGHTPAR
      { t }
  | TYPE
      { P_Type }

aterm:
  | t=sterm ts=sterm*
      { List.fold_left (fun t u -> P_Appl(t,u)) t ts }

term:
  | t=aterm
      { t }
  | x=pid COLON a=aterm ARROW b=term
      { P_Prod(x, Some(a), b) }
  | LEFTPAR x=ID COLON a=aterm RIGHTPAR ARROW b=term
      { P_Prod(x, Some(a), b) }
  | a=term ARROW b=term
      { P_Prod("_", Some(a), b) }
  | x=pid FATARROW t=term
      { P_Abst(x, None, t) }
  | x=pid COLON a=aterm FATARROW t=term
      { P_Abst(x, Some(a), t) }
%%
