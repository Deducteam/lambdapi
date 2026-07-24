open Lplib
open Common open Pos open Logger
open Syntax
open Core
open LpLexer
open Lexing
open Sedlexing
open OneLookaheadCellLexbuf

let log = Logger.make 'n' "pars" "parsing"
let log = log.pp

(* token management *)

let tokens = function
  | [] -> ""
  | s::l -> List.fold_left (fun acc s -> acc^", "^String.add_quotes s) s l

let string_of_token =
  let q = String.add_quotes in
  let (||) a b = a^", "^b in
  function
  | EOF -> "end of file"
  | ABORT -> q"abort"
  | ADMIT -> q"admit"
  | ADMITTED -> q"admitted"
  | ALL_HYPS -> q"all_hyps"
  | APPLY -> q"apply"
  | ARROW -> q"→"
  | AS -> q"as"
  | ASSERT _ -> q"assert" || q"assertnot"
  | ASSIGN -> q"≔"
  | ASSOCIATIVE -> q"associative"
  | ASSUME -> q"assume"
  | ASSUMPTION -> q"assumption"
  | BACKQUOTE -> q"`"
  | BEGIN -> q"begin"
  | BUILTIN -> q"builtin"
  | CHANGE -> q"change"
  | COERCE_RULE -> q"coerce_rule"
  | COLON -> q":"
  | COMMA -> q","
  | COMMUTATIVE -> q"commutative"
  | COMPUTE -> q"compute"
  | CONSTANT -> q"constant"
  | DEBUG -> q"debug"
  | DEBUG_FLAGS _ -> "debug flags"
  | DOT -> q"."
  | END -> q"end"
  | EQUIV -> q"≡"
  | EVAL -> q"eval"
  | EXISTS -> q"exists" (* only in Rocq *)
  | FAIL -> q"fail"
  | FIRST_HYP -> q"first_hyp"
  | FLAG -> q"flag"
  | FLOAT _ -> q"float"
  | FOCUS -> q"focus"
  | FORALL -> q"forall" (* only in Rocq *)
  | FUN -> q"fun"       (* only in Rocq *)
  | GENERALIZE -> q"generalize"
  | HAVE -> q"have"
  | HOOK_ARROW -> q"↪"
  | IN -> q"in"
  | INDUCTION -> q"induction"
  | INDUCTIVE -> q"inductive"
  | INFIX -> q"infix"
  | INJECTIVE -> q"injective"
  | INT _ -> q"integer"
  | LAMBDA -> q"λ"
  | LET -> q"let"
  | L_CU_BRACKET -> q"{"
  | L_PAREN -> q"("
  | L_SQ_BRACKET -> q"["
  | NOTATION -> q"notation"
  | OPAQUE -> q"opaque"
  | OPEN -> q"open"
  | ORELSE -> q"orelse"
  | PI -> q"Π"
  | POSTFIX -> q"postfix"
  | PREFIX -> q"prefix"
  | PRINT -> q"print"
  | PRIVATE -> q"private"
  | PROOFTERM -> q"proofterm"
  | PROTECTED -> q"protected"
  | PROVER -> q"prover"
  | PROVER_TIMEOUT -> q"prover_timeout"
  | QID _ -> "qualified identifier"
  | QID_EXPL _ -> "@-prefixed qualified identifier"
  | QINT _ -> "qualified integer"
  | QUANTIFIER -> q"quantifier"
  | REFINE -> q"refine"
  | REFLEXIVITY -> q"reflexivity"
  | REMOVE -> q"remove"
  | REPEAT -> q"repeat"
  | REQUIRE -> q"require"
  | REWRITE -> q"rewrite"
  | RULE -> q"rule"
  | R_CU_BRACKET -> q"}"
  | R_PAREN -> q")"
  | R_SQ_BRACKET -> q"]"
  | SEARCH -> q"search"
  | SEQUENTIAL -> q"sequential"
  | SEMICOLON -> q";"
  | SET -> q"set"
  | SIDE _ -> q"left" || q"right"
  | SIMPLIFY -> q"simplify"
  | SOLVE -> q"solve"
  | STRINGLIT _ -> "string literal"
  | SWITCH false -> q"off"
  | SWITCH true -> q"on" || q"off"
  | SYMBOL -> q"symbol"
  | SYMMETRY -> q"symmetry"
  | THICKARROW -> q"=>" (* only in Rocq *)
  | TRY -> q"try"
  | TURNSTILE -> q"⊢"
  | TYPE_QUERY -> q"type"
  | TYPE_TERM -> q"TYPE"
  | UID _ -> "non-qualified identifier"
  | UID_EXPL _ -> "@-prefixed non-qualified identifier"
  | UID_META _ -> "?-prefixed metavariable number"
  | UID_PATT _ -> "$-prefixed non-qualified identifier"
  | UNDERSCORE -> q"_"
  | UNIF_RULE -> q"unif_rule"
  | VBAR -> q"|"
  | VERBOSE -> q"verbose"
  | WHY3 -> q"why3"
  | WITH -> q"with"
  | TYPECLASS -> q"typeclass"
  | INSTANCE -> q"instance"

let string_of_tokens = List.fold_left (fun s t -> s^", "^string_of_token t)

let pp_token ppf t = Base.string ppf (string_of_token t)

let match_token tok patt =
 match patt,tok with
  | ASSERT _, ASSERT _
  | DEBUG_FLAGS _, DEBUG_FLAGS _
  | FLOAT _, FLOAT _
  | INT _, INT _
  | QID _, QID _
  | QID_EXPL _, QID_EXPL _
  | QINT _ , QINT _
  | SIDE _, SIDE _
  | STRINGLIT _, STRINGLIT _
  | SWITCH false, SWITCH false
  | SWITCH true, SWITCH _
  | UID _, UID _
  | UID_EXPL _, UID_EXPL _
  | UID_META _, UID_META _
  | UID_PATT _ , UID_PATT _ -> true
  | t1,t2 -> t1=t2

let match_guard patts lb =
 List.exists (match_token (current_token lb)) patts

let expected lb (msg:string) (tokens:token list) : 'a =
  if msg <> "" then syntax_error (current_pos lb) ("Expected: "^msg^".")
  else
    match tokens with
    | [] -> assert false
    | t::ts ->
      syntax_error (current_pos lb)
        (string_of_tokens ("Expected: "^string_of_token t)
           (ts @ get_expected_tokens lb)
        ^".")

(* building positions and terms *)

let extend_pos lb (lps:position * position) : 'a -> 'a loc =
  let p1 = fst lps and p2 = fst (current_pos lb) in
  let p2 =
    if p2.pos_cnum > p2.pos_bol then
      {p2 with pos_cnum = p2.pos_cnum - 1}
    else p2
  in
  (*if log_enabled() then
    log "extend_pos %s %a -> %a" s Pos.pp_lexing lps Pos.pp_lexing lps2;*)
  make_pos (p1,p2)

let qid_of_path (lps: position * position):
      string list -> (string list * string) loc = function
  | [] -> assert false
  | id::mp -> make_pos lps (List.rev mp, id)

let make_abst lb (pos1:position) (ps:p_params list) (t:p_term) (pos2:position)
    : p_term =
  if ps = [] then t
  else extend_pos lb (*__FUNCTION__*) (pos1,pos2) (P_Abst(ps,t))

let make_prod lb (pos1:position) (ps:p_params list) (t:p_term) (pos2:position)
    :p_term =
  if ps = [] then t
  else extend_pos lb (*__FUNCTION__*) (pos1,pos2) (P_Prod(ps,t))

let ident_of_term pos1 {elt; _} =
  match elt with
  | P_Iden({elt=([], x); pos}, _) -> Pos.make pos x
  | _ -> LpLexer.syntax_error pos1 "not an unqualified identifier."

(* generic parsing functions *)

let consume (token:token) (lb:'token lexbuf): unit =
  if current_token lb = token then consume_token lb
  else expected lb "" [token]

let prefix (token:token) (elt:'token lexbuf -> 'a) (lb:'token lexbuf): 'a =
  consume token lb; elt lb

let opt (tk : 'token) (lb:'token lexbuf) : bool =
  if log_enabled() then log "%s" __FUNCTION__;
  if current_token lb = tk then (consume_token lb; true)
  else (set_expected_tokens lb [tk]; false)

let list (guard: 'token list) (elt:'token lexbuf -> 'a) (lb:'token lexbuf)
 : 'a list =
  if log_enabled() then log "%s" __FUNCTION__;
  let acc = ref [] in
  while match_guard guard lb do acc := elt lb :: !acc done ;
  set_expected_tokens lb guard;
  List.rev !acc

let list_with_sep (guard: 'token list) (elt:'token lexbuf -> 'a) (sep:'token)
 (lb:'token lexbuf) : 'a list =
  if log_enabled() then log "%s" __FUNCTION__;
  let acc = ref [] in
  let guard = ref guard in
  let el = ref elt in
  while match_guard !guard lb do
    acc := !el lb :: !acc ;
    guard := [sep] ;
    el := prefix sep elt
  done ;
  set_expected_tokens lb !guard ;
  List.rev !acc

let list_with_sep_or_termin
 (guard: 'token list) (elt:'token lexbuf -> 'a) (sep:'token)
 (lb:'token lexbuf) : 'a list =
  if log_enabled() then log "%s" __FUNCTION__;
  let acc = ref [] in
  let match_sep = ref false in
  while match_guard (if !match_sep then [sep] else guard) lb do
    if !match_sep then (consume sep lb; match_sep := false)
    else (acc := elt lb :: !acc; match_sep := true)
  done ;
  set_expected_tokens lb (if !match_sep then [sep] else guard) ;
  List.rev !acc

let nelist (guard: 'token list) (elt:'token lexbuf -> 'a) (lb:'token lexbuf)
 : 'a list =
  if log_enabled() then log "%s" __FUNCTION__;
  let x = elt lb in
  x :: list guard elt lb

let nelist_with_sep (elt:'token lexbuf -> 'a) (sep:'token) (lb:'token lexbuf)
 : 'a list =
  if log_enabled() then log "%s" __FUNCTION__;
  let a = elt lb in
  let acc = list [sep] (prefix sep elt) lb in
  a::acc

(* parsing functions *)

let consume_STRINGLIT (lb:'token lexbuf): string =
  match current_token lb with
  | STRINGLIT s ->
      consume_token lb;
      s
  | _ ->
      expected lb "" [STRINGLIT""]

let consume_SWITCH (lb:'token lexbuf): bool =
  match current_token lb with
  | SWITCH b ->
      consume_token lb;
      b
  | _ ->
      expected lb "" [SWITCH true]

let consume_INT (lb:'token lexbuf): string =
  match current_token lb with
  | INT s ->
      consume_token lb;
      s
  | _ ->
      expected lb "" [INT""]

let qid (lb:'token lexbuf): (string list * string) loc =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | UID s ->
      let pos1 = current_pos lb in
      consume_token lb;
      make_pos pos1 ([], s)
  | QID p ->
      let pos1 = current_pos lb in
      consume_token lb;
      qid_of_path pos1 p
  | _ ->
      expected lb "" [UID"";QID[]]

let qid_or_regexp (lb:'token lexbuf): (string list * string) loc =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | UID s ->
      let pos1 = current_pos lb in
      consume_token lb;
      make_pos pos1 ([], s)
  | QID p ->
      let pos1 = current_pos lb in
      consume_token lb;
      qid_of_path pos1 p
  | STRINGLIT s ->
      let pos1 = current_pos lb in
      consume_token lb;
      make_pos pos1 ([], s)
  | _ ->
      expected lb "" [UID"";QID[];STRINGLIT""]

let qid_expl (lb:'token lexbuf): (string list * string) loc =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | UID_EXPL s ->
      let pos1 = current_pos lb in
      consume_token lb;
      make_pos pos1 ([], s)
  | QID_EXPL p ->
      let pos1 = current_pos lb in
      consume_token lb;
      qid_of_path pos1 p
  | _ ->
      expected lb "" [UID_EXPL"";QID_EXPL[]]

let uid (lb:'token lexbuf): string loc =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | UID s ->
      let pos1 = current_pos lb in
      consume_token lb;
      make_pos pos1 s
  | _ ->
      expected lb "" [UID""]

let sym_name (lb:'token lexbuf): string loc =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | INT s ->
      syntax_error (current_pos lb) "Forbidden symbol name."
  | UID s ->
      let pos1 = current_pos lb in
      consume_token lb;
      make_pos pos1 s
  | _ ->
      expected lb "" [UID""]

let param_tks = [UID"";UNDERSCORE]
let param (lb:'token lexbuf): string loc option =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | UID s ->
      let pos1 = current_pos lb in
      consume_token lb;
      Some (make_pos pos1 s)
  | UNDERSCORE ->
      consume_token lb;
      None
  | _ ->
      expected lb "" param_tks

let int (lb:'token lexbuf): string =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | INT s ->
      consume_token lb;
      s
  | _ ->
      expected lb "" [INT""]

let float_or_int (lb:'token lexbuf): string =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | INT s
  | FLOAT s ->
      consume_token lb;
      s
  | _ ->
      expected lb "" [FLOAT"";INT""]

let path_tks = [QID[]]
let path (lb:'token lexbuf): string list loc =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | QID p ->
      let pos1 = current_pos lb in
      consume_token lb;
      make_pos pos1 (List.rev p)
  | _ ->
      expected lb "" path_tks

let proof_end_tks = [END;ABORT;ADMITTED]

let print (lb:'token lexbuf): print =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | SEMICOLON | ABORT | ADMITTED | END ->
    Goal
  | UID s ->
    let pos1 = current_pos lb in
    consume_token lb;
    Symbol(make_pos pos1 ([],s))
  | QID p ->
    let pos1 = current_pos lb in
    consume_token lb;
    Symbol(qid_of_path pos1 p)
  | STRINGLIT s ->
    consume_token lb;
    String (String.remove_quotes s)
  | UNIF_RULE ->
    consume_token lb;
    Unif_rule
  | COERCE_RULE ->
    consume_token lb;
    Coerce_rule
  | VERBOSE ->
    consume_token lb;
    Verbose
  | DEBUG ->
    consume_token lb;
    Debug
  | FLAG ->
    consume_token lb;
    Flag
  | PROVER ->
    consume_token lb;
    Prover
  | PROVER_TIMEOUT ->
    consume_token lb;
    Prover_timeout
  | BUILTIN ->
    consume_token lb;
    Builtin
  | _ ->
    expected lb ""
      ([UID"";QID[];STRINGLIT"";UNIF_RULE;COERCE_RULE;VERBOSE;
        DEBUG;FLAG;PROVER;PROVER_TIMEOUT;BUILTIN;SEMICOLON] @ proof_end_tks)

let term_id (lb:'token lexbuf): p_term =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | UID _
  | QID _ ->
      let i = qid lb in
      {i with elt=P_Iden(i, false)}
  | UID_EXPL _
  | QID_EXPL _ ->
      let i = qid_expl lb in
      {i with elt=P_Iden(i, true)}
  | _ ->
      expected lb "" [UID"";QID[];UID_EXPL"";QID_EXPL[]]

(* commands *)

(* [req] tells whether the command starts with the [require] keyword:
   [require [private] open] loads the modules and opens them
   ([P_require]), while a bare [[private] open] only opens modules
   that are already loaded ([P_open]). For a bare open, the position
   of the "open" keyword is recorded in the AST (a "private" modifier,
   like modifiers of symbol declarations, is not part of the
   keyword). *)
let open_ (req:bool) (priv:bool) (lb:'token lexbuf) : p_command_aux =
 if log_enabled() then log "%s" __FUNCTION__;
 let kw_pos = Some(locate (current_pos lb)) in
 consume OPEN lb;
 let ps = nelist path_tks path lb in
 if req then P_require(Some priv,ps) else P_open(kw_pos,priv,ps)

let rec symbol (p_sym_mod:p_modifier list) (lb:'token lexbuf): p_command_aux =
 if log_enabled() then log "%s" __FUNCTION__;
 let p_sym_kw = Some(locate (current_pos lb)) in
 consume SYMBOL lb;
 let p_sym_nam = sym_name lb in
 let p_sym_arg = list params_tks params lb in
 begin
   match current_token lb with
   | COLON ->
       consume_token lb;
       let p_sym_typ = Some(term lb) in
       begin
         match current_token lb with
         | BEGIN ->
             consume_token lb;
             let p_sym_prf = Some (proof lb) in
             let p_sym_def = false in
             let sym =
               {p_sym_mod; p_sym_kw; p_sym_nam; p_sym_arg; p_sym_typ;
                p_sym_trm=None; p_sym_def; p_sym_prf}
             in P_symbol(sym)
         | ASSIGN ->
             consume_token lb;
             let p_sym_trm, p_sym_prf = term_proof lb in
             let p_sym_def = true in
             let sym =
               {p_sym_mod; p_sym_kw; p_sym_nam; p_sym_arg; p_sym_typ;
                p_sym_trm; p_sym_def; p_sym_prf}
             in P_symbol(sym)
         | SEMICOLON ->
             let p_sym_trm = None in
             let p_sym_def = false in
             let p_sym_prf = None in
             let sym =
               {p_sym_mod; p_sym_kw; p_sym_nam; p_sym_arg; p_sym_typ;
                p_sym_trm; p_sym_def; p_sym_prf}
             in P_symbol(sym)
         | _ ->
             expected lb "" [BEGIN;ASSIGN;SEMICOLON]
       end
   | ASSIGN ->
       consume_token lb;
       let p_sym_trm, p_sym_prf = term_proof lb in
       let p_sym_def = true in
       let p_sym_typ = None in
       let sym =
         {p_sym_mod; p_sym_kw; p_sym_nam; p_sym_arg; p_sym_typ;
          p_sym_trm; p_sym_def; p_sym_prf}
       in P_symbol(sym)
   | _ ->
       expected lb "" [COLON;ASSIGN]
 end

and inductive_cmd (p_sym_mod:p_modifier list) (lb:'token lexbuf)
: p_command_aux =
 if log_enabled() then log "%s" __FUNCTION__;
 let xs = list params_tks params lb in
 match current_token lb with
 | INDUCTIVE ->
     let kw_pos = Some(locate (current_pos lb)) in
     consume INDUCTIVE lb;
     let i = inductive lb in
     let is = list [WITH] (prefix WITH inductive) lb in
     P_inductive(kw_pos,p_sym_mod,xs,i::is)
 | _ -> expected lb "" [L_PAREN;L_SQ_BRACKET;INDUCTIVE]

and command (lb:'token lexbuf) : p_command =
 if log_enabled() then log "%s" __FUNCTION__;
 let pos1 = current_pos lb in
 let p_sym_mod = list modifier_tks modifier lb in
 match p_sym_mod with
 | [{elt=P_expo Term.Privat;_}] ->
    begin match current_token lb with
    | OPEN -> extend_pos lb (*__FUNCTION__*) pos1 (open_ false true lb)
    | SYMBOL ->
        extend_pos lb (*__FUNCTION__*) pos1 (symbol p_sym_mod lb)
    | L_PAREN
    | L_SQ_BRACKET
    | INDUCTIVE ->
        extend_pos lb (*__FUNCTION__*) pos1 (inductive_cmd p_sym_mod lb)
    | _ -> expected lb "" [OPEN;SYMBOL;L_PAREN;L_SQ_BRACKET;INDUCTIVE]
    end
 | [{elt;_}] when List.mem elt [P_opaq; P_typeclass; P_typeclass_instance] ->
    begin match current_token lb with
    | UID _
    | QID _ ->
       let i = qid lb in
       let cmd = match elt with
         | P_opaq -> P_opaque i
         | P_typeclass -> P_type_class i
         | P_typeclass_instance -> P_type_class_instance i
         | _ -> assert false
       in
       extend_pos lb (*__FUNCTION__*) pos1 cmd
    | SYMBOL ->
       extend_pos lb (*__FUNCTION__*) pos1 (symbol p_sym_mod lb)
    | _ -> expected lb "" [UID"";QID[];SYMBOL]
    end
 | _::_ ->
    begin match current_token lb with
    | SYMBOL ->
       extend_pos lb (*__FUNCTION__*) pos1 (symbol p_sym_mod lb)
    | L_PAREN
    | L_SQ_BRACKET
    | INDUCTIVE ->
        extend_pos lb (*__FUNCTION__*) pos1 (inductive_cmd p_sym_mod lb)
    | _ -> expected lb "" [SYMBOL;L_PAREN;L_SQ_BRACKET;INDUCTIVE]
    end
 | [] ->
    begin match current_token lb with
    | REQUIRE ->
        consume_token lb;
        begin
          match current_token lb with
          | OPEN ->
              extend_pos lb (*__FUNCTION__*) pos1 (open_ true false lb)
          | PRIVATE ->
              consume_token lb;
              extend_pos lb (*__FUNCTION__*) pos1 (open_ true true lb)
          | QID _ ->
              let ps = nelist path_tks path lb in
              begin
                match current_token lb with
                | AS ->
                    let p =
                      match ps with
                      | [p] -> p
                      | _ -> expected lb "a single module before \"as\"" []
                    in
                    consume_token lb;
                    let i = uid lb in
                    extend_pos lb (*__FUNCTION__*) pos1 (P_require_as(p,i))
                | _ ->
                    set_expected_tokens lb [AS] ;
                    extend_pos lb (*__FUNCTION__*) pos1 (P_require(None,ps))
              end
          | _ -> expected lb "" [OPEN;PRIVATE;QID[]]
        end
    | OPEN ->
        extend_pos lb (*__FUNCTION__*) pos1 (open_ false false lb)
    | SYMBOL ->
        extend_pos lb (*__FUNCTION__*) pos1 (symbol p_sym_mod lb)
    | L_PAREN
    | L_SQ_BRACKET
    | INDUCTIVE ->
        extend_pos lb (*__FUNCTION__*) pos1 (inductive_cmd p_sym_mod lb)
    | RULE ->
        consume_token lb;
        let rs = list_with_sep (rule_tks ()) rule WITH lb in
        extend_pos lb (*__FUNCTION__*) pos1 (P_rules rs)
    | UNIF_RULE ->
        consume_token lb;
        let e = equation lb in
        consume HOOK_ARROW lb;
        consume L_SQ_BRACKET lb;
        let es = list_with_sep (equation_tks ()) equation SEMICOLON lb in
        consume R_SQ_BRACKET lb;
        (* FIXME: give sensible positions instead of Pos.none and P.appl. *)
        let equiv = P.qiden Sign.Ghost.path Unif_rule.equiv.sym_name in
        let cons = P.qiden Sign.Ghost.path Unif_rule.cons.sym_name in
        let mk_equiv (t, u) = P.appl (P.appl equiv t) u in
        let lhs = mk_equiv e in
        let es = List.rev_map mk_equiv es in
        let (en, es) = List.(hd es, tl es) in
        let cat e es = P.appl (P.appl cons e) es in
        let rhs = List.fold_right cat es en in
        let r = extend_pos lb (*__FUNCTION__*) pos1 (lhs, rhs) in
        extend_pos lb (*__FUNCTION__*) pos1 (P_unif_rule(r))
    | COERCE_RULE ->
        consume_token lb;
        let r = rule lb in
        extend_pos lb (*__FUNCTION__*) pos1 (P_coercion r)
    | BUILTIN ->
        consume_token lb;
        begin
          let s = consume_STRINGLIT lb in
          consume ASSIGN lb;
          let s = String.remove_quotes s and i = qid lb in
          extend_pos lb (*__FUNCTION__*) pos1 (P_builtin(s,i))
        end
    | NOTATION ->
        consume_token lb;
        let i = qid lb in
        let n = notation lb in
        extend_pos lb (*__FUNCTION__*) pos1 (P_notation(i,n))
    | ASSERT _
    | COMPUTE
    | DEBUG
    | FLAG
    | PRINT
    | PROOFTERM
    | PROVER
    | PROVER_TIMEOUT
    | SEARCH
    | TYPE_QUERY
    | VERBOSE ->
        let q = query lb in
        extend_pos lb (*__FUNCTION__*) pos1 (P_query(q))
    | _ ->
      expected lb "command"
        (modifier_tks @
         [REQUIRE;OPEN;SYMBOL;L_PAREN;L_SQ_BRACKET;INDUCTIVE;RULE;UNIF_RULE;
          COERCE_RULE;BUILTIN;NOTATION] @ (query_tks()))
    end

and inductive (lb:'token lexbuf): p_inductive =
  let pos0 = current_pos lb in
  let i = uid lb in
  let pos1 = current_pos lb in
  let ps = list params_tks params lb in
  consume COLON lb;
  let t = term lb in
  let pos2 = current_pos lb in
  let t = make_prod lb (fst pos1) ps t (snd pos2) in
  consume ASSIGN lb;
  begin
    match current_token lb with
    | UID _ ->
        let l = nelist_with_sep constructor VBAR lb in
        extend_pos lb (*__FUNCTION__*) pos0 (i,t,l)
    | VBAR ->
        let l = list [VBAR] (prefix VBAR constructor) lb in
        extend_pos lb (*__FUNCTION__*) pos0 (i,t,l)
    | SEMICOLON ->
        let l = [] in
        extend_pos lb (*__FUNCTION__*) pos0 (i,t,l)
    | _ ->
        expected lb "" [UID"";VBAR;SEMICOLON]
    end

and constructor (lb:'token lexbuf): p_ident * p_term =
  let i = uid lb in
  let pos1 = current_pos lb in
  let ps = list params_tks params lb in
  consume COLON lb;
  let t = term lb in
  i, make_prod lb (fst pos1) ps t (snd (current_pos lb))

and modifier_tks =
  [SIDE Pratter.Left;ASSOCIATIVE;COMMUTATIVE;CONSTANT;INJECTIVE;OPAQUE;
   PRIVATE;PROTECTED;SEQUENTIAL;TYPECLASS;INSTANCE]
and modifier (lb:'token lexbuf): p_modifier =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | SIDE d ->
      let pos1 = current_pos lb in
      consume_token lb;
      consume ASSOCIATIVE lb;
      extend_pos lb (*__FUNCTION__*) pos1
        (P_prop (Term.Assoc((d = Pratter.Left))))
  | ASSOCIATIVE ->
      let pos1 = current_pos lb in
      consume_token lb;
      extend_pos lb (*__FUNCTION__*) pos1 (P_prop (Term.Assoc false))
  | COMMUTATIVE ->
      let pos1 = current_pos lb in
      consume_token lb;
      extend_pos lb (*__FUNCTION__*) pos1 (P_prop Term.Commu)
  | CONSTANT ->
      let pos1 = current_pos lb in
      consume_token lb;
      extend_pos lb (*__FUNCTION__*) pos1 (P_prop Term.Const)
  | INJECTIVE ->
      let pos1 = current_pos lb in
      consume_token lb;
      extend_pos lb (*__FUNCTION__*) pos1 (P_prop Term.Injec)
  | OPAQUE ->
      let pos1 = current_pos lb in
      consume_token lb;
      extend_pos lb (*__FUNCTION__*) pos1 P_opaq
  | TYPECLASS ->
      let pos1 = current_pos lb in
      consume_token lb;
      extend_pos lb (*__FUNCTION__*) pos1 P_typeclass
  | INSTANCE ->
      let pos1 = current_pos lb in
      consume_token lb;
      extend_pos lb (*__FUNCTION__*) pos1 P_typeclass_instance
  | PRIVATE ->
      let pos1 = current_pos lb in
      consume_token lb;
      extend_pos lb (*__FUNCTION__*) pos1 (P_expo Term.Privat)
  | PROTECTED ->
      let pos1 = current_pos lb in
      consume_token lb;
      extend_pos lb (*__FUNCTION__*) pos1 (P_expo Term.Protec)
  | SEQUENTIAL ->
      let pos1 = current_pos lb in
      consume_token lb;
      extend_pos lb (*__FUNCTION__*) pos1 (P_mstrat Term.Sequen)
  | _ ->
      expected lb "" modifier_tks

and notation (lb:'token lexbuf): string Term.notation =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | INFIX ->
      consume_token lb;
      begin
        match current_token lb with
        | SIDE d ->
            consume_token lb;
            let p = float_or_int lb in
            Term.Infix(d, p)
        | INT _
        | FLOAT _ ->
            let p = float_or_int lb in
            Term.Infix(Pratter.Neither, p)
        | _ -> expected lb "" [SIDE Pratter.Left;INT"";FLOAT""]
      end
  | POSTFIX ->
      consume_token lb;
      let p = float_or_int lb in
      Term.Postfix p
  | PREFIX ->
      consume_token lb;
      let p = float_or_int lb in
      Term.Prefix p
  | QUANTIFIER ->
      consume_token lb;
      Term.Quant
  | _ ->
      expected lb "" [INFIX;POSTFIX;PREFIX;QUANTIFIER]

and rule_tks () = term_tks
and rule (lb:'token lexbuf): (p_term * p_term) loc =
  if log_enabled() then log "%s" __FUNCTION__;
  let pos1 = current_pos lb in
  let l = term lb in
  consume HOOK_ARROW lb;
  let r = term lb in
  extend_pos lb (*__FUNCTION__*) pos1 (l, r)

and equation_tks () = term_tks
and equation (lb:'token lexbuf): p_term * p_term =
  if log_enabled() then log "%s" __FUNCTION__;
  let l = term lb in
  consume EQUIV lb;
  let r = term lb in
  (l, r)

(* queries *)

and query_tks() = [ASSERT false;COMPUTE;DEBUG;FLAG;PRINT;PROOFTERM;PROVER;
                   PROVER_TIMEOUT;TYPE_QUERY;VERBOSE;SEARCH]
and query (lb:'token lexbuf): p_query =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | ASSERT b ->
      let pos1 = current_pos lb in
      consume_token lb;
      let ps = list params_tks params lb in
      consume TURNSTILE lb;
      let t = term lb in
      begin
        match current_token lb with
        | COLON ->
            consume_token lb;
            let a = term lb in
            let pos2 = current_pos lb in
            let t = make_abst lb (snd pos1) ps t (fst pos2) in
            let a = make_prod lb (snd pos1) ps a (fst pos2) in
            extend_pos lb (*__FUNCTION__*) pos1
              (P_query_assert(b, P_assert_typing(t,a)))
        | EQUIV ->
            consume_token lb;
            let u = term lb in
            let pos2 = current_pos lb in
            let t = make_abst lb (snd pos1) ps t (fst pos2) in
            let u = make_abst lb (snd pos1) ps u (fst pos2) in
            extend_pos lb (*__FUNCTION__*) pos1
              (P_query_assert(b, P_assert_conv(t, u)))
        | _ ->
            expected lb "" [COLON;EQUIV]
      end
  | COMPUTE ->
      let pos1 = current_pos lb in
      consume_token lb;
      let t = term lb in
      extend_pos lb (*__FUNCTION__*) pos1
        (P_query_normalize(t, {strategy=SNF; steps=None}))
  | DEBUG ->
      let pos1 = current_pos lb in
      consume_token lb;
      begin
        match current_token lb with
        | SEMICOLON | ABORT | ADMITTED | END ->
          extend_pos lb (*__FUNCTION__*) pos1 (P_query_print Debug)
        | DEBUG_FLAGS(b,s) ->
          consume_token lb;
          extend_pos lb (*__FUNCTION__*) pos1 (P_query_debug(b,s))
        | _ ->
          expected lb "" ([DEBUG_FLAGS(true,"");SEMICOLON] @ proof_end_tks)
      end
  | FLAG ->
      let pos1 = current_pos lb in
      consume_token lb;
      begin
        match current_token lb with
        | SEMICOLON | ABORT | ADMITTED | END ->
            extend_pos lb (*__FUNCTION__*) pos1 (P_query_print Flag)
        | STRINGLIT s ->
          consume_token lb;
          let b = consume_SWITCH lb in
          let s = String.remove_quotes s in
          extend_pos lb (*__FUNCTION__*) pos1 (P_query_flag(s,b))
        | _ ->
          expected lb "" ([STRINGLIT"";SEMICOLON] @ proof_end_tks)
      end
  | PRINT ->
      let pos1 = current_pos lb in
      consume_token lb;
      let p = print lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_query_print p)
  | PROOFTERM ->
      let pos1 = current_pos lb in
      consume_token lb;
      extend_pos lb (*__FUNCTION__*) pos1 P_query_proofterm
  | PROVER ->
      let pos1 = current_pos lb in
      consume_token lb;
      begin
        match current_token lb with
        | SEMICOLON | ABORT | ADMITTED | END ->
            extend_pos lb (*__FUNCTION__*) pos1 (P_query_print Prover)
        | STRINGLIT s ->
          consume_token lb;
          let s = String.remove_quotes s in
          extend_pos lb (*__FUNCTION__*) pos1 (P_query_prover s)
        | _ ->
          expected lb "" ([STRINGLIT"";SEMICOLON] @ proof_end_tks)
      end
  | PROVER_TIMEOUT ->
      let pos1 = current_pos lb in
      consume_token lb;
      begin
        match current_token lb with
        | SEMICOLON | ABORT | ADMITTED | END ->
            extend_pos lb (*__FUNCTION__*) pos1 (P_query_print Prover_timeout)
        | INT s ->
          consume_token lb;
          extend_pos lb (*__FUNCTION__*) pos1 (P_query_prover_timeout s)
        | _ ->
          expected lb "" ([INT"";SEMICOLON] @ proof_end_tks)
      end
  | SEARCH ->
      let pos1 = current_pos lb in
      consume_token lb;
      let q = search lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_query_search q)
  | TYPE_QUERY ->
      let pos1 = current_pos lb in
      consume_token lb;
      let t = term lb in
      extend_pos lb (*__FUNCTION__*) pos1
        (P_query_infer(t, {strategy=NONE; steps=None}))
  | VERBOSE ->
      let pos1 = current_pos lb in
      consume_token lb;
      begin
        match current_token lb with
        | SEMICOLON | ABORT | ADMITTED | END ->
          extend_pos lb (*__FUNCTION__*) pos1 (P_query_print Verbose)
        | INT s ->
          consume_token lb;
          extend_pos lb (*__FUNCTION__*) pos1 (P_query_verbose s)
        | _ ->
          expected lb "" ([INT"";SEMICOLON] @ proof_end_tks)
      end
  | _ ->
      expected lb "" (query_tks())

and term_proof (lb:'token lexbuf):
 p_term option * (p_proof * p_proof_end) option =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | BEGIN ->
      consume_token lb;
      let p = proof lb in
      None, Some p
  (* bterm *)
  | BACKQUOTE
  | PI
  | LAMBDA
  | LET
  (* aterm *)
  | UID _
  | QID _
  | UID_EXPL _
  | QID_EXPL _
  | UNDERSCORE
  | TYPE_TERM
  | UID_META _
  | UID_PATT _
  | L_PAREN
  | L_SQ_BRACKET
  | INT _
  | QINT _
  | STRINGLIT _ ->
      let t = term lb in
      if opt BEGIN lb then
       let p = proof lb in
       Some t, Some p
      else
       Some t, None
  | _ ->
      expected lb "term or proof" []

(* proofs *)

and proof (lb:'token lexbuf): p_proof * p_proof_end =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | L_CU_BRACKET ->
      let l = nelist subproof_tks subproof lb in
      if current_token lb = SEMICOLON then consume_token lb;
      let pe = proof_end lb in
      l, pe
  (*queries*)
  | ASSERT _
  | COMPUTE
  | DEBUG
  | FLAG
  | PRINT
  | PROOFTERM
  | PROVER
  | PROVER_TIMEOUT
  | SEARCH
  | TYPE_QUERY
  | VERBOSE
  (*tactics*)
  | ADMIT
  | ALL_HYPS
  | APPLY
  | ASSUME
  | CHANGE
  | EVAL
  | FAIL
  | FIRST_HYP
  | FOCUS
  | GENERALIZE
  | HAVE
  | INDUCTION
  | ORELSE
  | REFINE
  | REFLEXIVITY
  | REMOVE
  | REPEAT
  | REWRITE
  | SET
  | SIMPLIFY
  | SOLVE
  | SYMMETRY
  | TRY
  | WHY3 ->
      let l = steps lb in
      let pe = proof_end lb in
      [l], pe
  | END
  | ABORT
  | ADMITTED ->
      let pe = proof_end lb in
      [], pe
  | _ ->
    expected lb
      (string_of_tokens "subproof, tactic, query" proof_end_tks) []

and subproof_tks = [L_CU_BRACKET]
and subproof (lb:'token lexbuf): p_proofstep list =
  if log_enabled() then log "%s" __FUNCTION__;
  consume L_CU_BRACKET lb;
  let l = steps lb in
  consume R_CU_BRACKET lb;
  l

and steps (lb:'token lexbuf): p_proofstep list =
  if log_enabled() then log "%s" __FUNCTION__;
  list_with_sep_or_termin (step_tks ()) step SEMICOLON lb

and step_tks() = tactic_tks()
and step (lb:'token lexbuf): p_proofstep =
  if log_enabled() then log "%s" __FUNCTION__;
  let t = tactic lb in
  let l = list subproof_tks subproof lb in
  Tactic(t, l)

and proof_end (lb:'token lexbuf): p_proof_end =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | ABORT ->
      let pos1 = current_pos lb in
      consume_token lb;
      make_pos pos1 Syntax.P_proof_abort
  | ADMITTED ->
      let pos1 = current_pos lb in
      consume_token lb;
      make_pos pos1 Syntax.P_proof_admitted
  | END ->
      let pos1 = current_pos lb in
      consume_token lb;
      make_pos pos1 Syntax.P_proof_end
  | _ ->
      expected lb "" proof_end_tks

and tactic_tks() =
  [ADMIT;ALL_HYPS;APPLY;ASSUME;ASSUMPTION;CHANGE;EVAL;FAIL;FIRST_HYP;FOCUS;
   GENERALIZE;HAVE;INDUCTION;ORELSE;REFINE;REFLEXIVITY;REMOVE;REPEAT;REWRITE;
   SET;SIMPLIFY;SOLVE;SYMMETRY;TRY;WHY3] @ (query_tks())
and tactic (lb:'token lexbuf): p_tactic =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  (*queries*)
  | ASSERT _
  | COMPUTE
  | DEBUG
  | FLAG
  | PRINT
  | PROOFTERM
  | PROVER
  | PROVER_TIMEOUT
  | SEARCH
  | TYPE_QUERY
  | VERBOSE ->
      let pos1 = current_pos lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_tac_query (query lb))
  | ADMIT ->
      let pos1 = current_pos lb in
      consume_token lb;
      make_pos pos1 P_tac_admit
  | ALL_HYPS ->
      let pos1 = current_pos lb in
      consume_token lb;
      let t = term lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_tac_all_hyps t)
  | APPLY ->
      let pos1 = current_pos lb in
      consume_token lb;
      let t = term lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_tac_apply t)
  | ASSUME ->
      let pos1 = current_pos lb in
      consume_token lb;
      let xs = nelist params_tks param lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_tac_assume xs)
  | ASSUMPTION ->
      let pos1 = current_pos lb in
      consume_token lb;
      make_pos pos1 P_tac_assumption
  | CHANGE ->
      let pos1 = current_pos lb in
      consume_token lb;
      let t = term lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_tac_change t)
  | EVAL ->
      let pos1 = current_pos lb in
      consume_token lb;
      let t = term lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_tac_eval t)
  | FAIL ->
      let pos1 = current_pos lb in
      consume_token lb;
      make_pos pos1 P_tac_fail
  | FIRST_HYP ->
      let pos1 = current_pos lb in
      consume_token lb;
      let t = term lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_tac_first_hyp t)
  | FOCUS ->
      let pos1 = current_pos lb in
      consume_token lb;
      let n = consume_INT lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_tac_focus n)
  | GENERALIZE ->
      let pos1 = current_pos lb in
      consume_token lb;
      let i = uid lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_tac_generalize i)
  | HAVE ->
      let pos1 = current_pos lb in
      consume_token lb;
      let i = uid lb in
      consume COLON lb;
      let t = term lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_tac_have(i,t))
  | INDUCTION ->
      let pos1 = current_pos lb in
      consume_token lb;
      make_pos pos1 P_tac_induction
  | ORELSE ->
      let pos1 = current_pos lb in
      consume_token lb;
      let t1 = tactic lb in
      let t2 = tactic lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_tac_orelse(t1,t2))
  | REFINE ->
      let pos1 = current_pos lb in
      consume_token lb;
      let t = term lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_tac_refine t)
  | REFLEXIVITY ->
      let pos1 = current_pos lb in
      consume_token lb;
      make_pos pos1 P_tac_refl
  | REMOVE ->
      let pos1 = current_pos lb in
      consume_token lb;
      let xs = nelist [UID""] uid lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_tac_remove xs)
  | REPEAT ->
      let pos1 = current_pos lb in
      consume_token lb;
      let t = tactic lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_tac_repeat t)
  | REWRITE ->
      let pos1 = current_pos lb in
      consume_token lb;
      begin
        match current_token lb with
        | SIDE d ->
            consume_token lb;
            if opt DOT lb then
              let p = rwpatt_bracket lb in
              let t = term lb in
              let b = d <> Pratter.Left in
              extend_pos lb (*__FUNCTION__*) pos1
               (P_tac_rewrite(b,Some p,t))
            else
              let t = term lb in
              let b = d <> Pratter.Left in
              extend_pos lb (*__FUNCTION__*) pos1
               (P_tac_rewrite(b,None,t))
        | DOT ->
            consume_token lb;
            let p = rwpatt_bracket lb in
            let t = term lb in
            extend_pos lb (*__FUNCTION__*) pos1 (P_tac_rewrite(true,Some p,t))
        | _ ->
            set_expected_tokens lb [SIDE Pratter.Left;DOT] ;
            let t = term lb in
            extend_pos lb (*__FUNCTION__*) pos1 (P_tac_rewrite(true,None,t))
      end
  | SET ->
      let pos1 = current_pos lb in
      consume_token lb;
      let i = uid lb in
      consume ASSIGN lb;
      let t = term lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_tac_set(i,t))
  | SIMPLIFY ->
      let pos1 = current_pos lb in
      consume_token lb;
      begin
        match current_token lb with
        | UID _
        | QID _ ->
            extend_pos lb (*__FUNCTION__*) pos1 (P_tac_simpl(SimpSym(qid lb)))
        | RULE ->
            consume_token lb;
            consume (SWITCH false) lb;
            extend_pos lb (*__FUNCTION__*) pos1 (P_tac_simpl SimpBetaOnly)
        | _ ->
            set_expected_tokens lb [UID"";QID[];RULE];
            extend_pos lb (*__FUNCTION__*) pos1 (P_tac_simpl SimpAll)
      end
  | SOLVE ->
      let pos1 = current_pos lb in
      consume_token lb;
      make_pos pos1 P_tac_solve
  | SYMMETRY ->
      let pos1 = current_pos lb in
      consume_token lb;
      make_pos pos1 P_tac_sym
  | TRY ->
      let pos1 = current_pos lb in
      consume_token lb;
      let t = tactic lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_tac_try t)
  | WHY3 ->
      let pos1 = current_pos lb in
      consume_token lb;
      begin
        match current_token lb with
        | STRINGLIT s -> let s = String.remove_quotes s in
            extend_pos lb (*__FUNCTION__*) pos1 (P_tac_why3 (Some s))
        | _ ->
            set_expected_tokens lb [STRINGLIT""] ;
            make_pos pos1 (P_tac_why3 None)
      end
  | _ ->
      expected lb "tactic or query" (tactic_tks())

and rwpatt_content (lb:'token lexbuf): p_rwpatt =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  (* bterm *)
  | BACKQUOTE
  | PI
  | LAMBDA
  | LET
  (* aterm *)
  | UID _
  | QID _
  | UID_EXPL _
  | QID_EXPL _
  | UNDERSCORE
  | TYPE_TERM
  | UID_META _
  | UID_PATT _
  | L_PAREN
  | L_SQ_BRACKET
  | INT _
  | QINT _
  | STRINGLIT _ ->
      let pos1 = current_pos lb in
      let t1 = term lb in
      begin
        match current_token lb with
        | IN ->
            consume_token lb;
            let t2 = term lb in
            if opt IN lb then
              let t3 = term lb in
              let x = ident_of_term pos1 t2 in
              extend_pos lb (*__FUNCTION__*) pos1
                (Rw_TermInIdInTerm(t1,(x,t3)))
            else
              let x = ident_of_term pos1 t1 in
               extend_pos lb (*__FUNCTION__*) pos1 (Rw_IdInTerm(x,t2))
        | AS ->
            consume_token lb;
            let t2 = term lb in
            consume IN lb;
            let t3 = term lb in
            let x = ident_of_term pos1 t2 in
            extend_pos lb (*__FUNCTION__*) pos1 (Rw_TermAsIdInTerm(t1,(x,t3)))
        | _ ->
            set_expected_tokens lb [IN;AS];
            extend_pos lb (*__FUNCTION__*) pos1 (Rw_Term(t1))
      end
  | IN ->
      let pos1 = current_pos lb in
      consume_token lb;
      let t1 = term lb in
      if opt IN lb then
        let t2 = term lb in
        let x = ident_of_term pos1 t1 in
        extend_pos lb (*__FUNCTION__*) pos1 (Rw_InIdInTerm(x,t2))
      else
        extend_pos lb (*__FUNCTION__*) pos1 (Rw_InTerm(t1))
  | _ ->
      expected lb (string_of_tokens "term" [IN]) []

and rwpatt_bracket (lb:'token lexbuf): p_rwpatt =
  if log_enabled() then log "%s" __FUNCTION__;
  consume L_SQ_BRACKET lb;
  let p = rwpatt_content lb in
  consume R_SQ_BRACKET lb; (*add info on opening bracket*)
  p

and rwpatt (lb:'token lexbuf): p_rwpatt =
  if log_enabled() then log "%s" __FUNCTION__;
  consume DOT lb;
  rwpatt_bracket lb

(* terms *)

and params_tks = [L_PAREN;L_SQ_BRACKET;UID"";UNDERSCORE]
and params (lb:'token lexbuf): p_params =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | L_PAREN ->
      consume_token lb;
      let ps = nelist param_tks param lb in
      begin
        match current_token lb with
        | COLON ->
            consume_token lb;
            let typ = term lb in
            consume R_PAREN lb;
            ps, Some typ, false
        | R_PAREN ->
            consume_token lb;
            ps, None, false
        | _ ->
            expected lb "" [COLON;R_PAREN]
      end
  | L_SQ_BRACKET ->
      consume_token lb;
      let ps = nelist param_tks param lb in
      begin
        match current_token lb with
        | COLON ->
            consume_token lb;
            let typ = term lb in
            consume R_SQ_BRACKET lb;
            ps, Some typ, true
        | R_SQ_BRACKET ->
            consume_token lb;
            ps, None, true
        | _ ->
            expected lb "" [COLON;R_SQ_BRACKET]
      end
  | UID _
  | UNDERSCORE ->
      let x = param lb in
      [x], None, false
  | _ ->
      expected lb "" params_tks

and term_tks =
  [BACKQUOTE;(*EXISTS;FORALL;FUN;*)PI;LAMBDA;LET;
   UID"";QID[];UID_EXPL"";QID_EXPL[];UNDERSCORE;
   TYPE_TERM;UID_META 0;UID_PATT"";L_PAREN;L_SQ_BRACKET;
   INT"";QINT([],"");STRINGLIT""]
and term (lb:'token lexbuf): p_term =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  (* bterm *)
  | BACKQUOTE
  | EXISTS (* only in Rocq *)
  | FORALL (* only in Rocq *)
  | FUN    (* only in Rocq *)
  | PI
  | LAMBDA
  | LET ->
      bterm lb
  (* aterm *)
  | UID _
  | QID _
  | UID_EXPL _
  | QID_EXPL _
  | UNDERSCORE
  | TYPE_TERM
  | UID_META _
  | UID_PATT _
  | L_PAREN
  | L_SQ_BRACKET
  | INT _
  | QINT _
  | STRINGLIT _ ->
      let pos1 = current_pos lb in
      let h = aterm lb in
      app pos1 h lb
  | _ ->
      expected lb "term" term_tks

and app (pos1:position * position) (t: p_term) (lb:'token lexbuf): p_term =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  (* aterm *)
  | UID _
  | QID _
  | UID_EXPL _
  | QID_EXPL _
  | UNDERSCORE
  | TYPE_TERM
  | UID_META _
  | UID_PATT _
  | L_PAREN
  | L_SQ_BRACKET
  | INT _
  | QINT _
  | STRINGLIT _ ->
      let u = aterm lb in
      app pos1 (extend_pos lb (*__FUNCTION__*) pos1 (P_Appl(t,u))) lb
  (* bterm *)
  | BACKQUOTE
  | PI
  | LAMBDA
  | LET ->
      let u = bterm lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_Appl(t,u))
  (* other cases *)
  | ARROW ->
      consume_token lb;
      let u = term lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_Arro(t,u))
  | _ ->
      t

and bterm (lb:'token lexbuf): p_term =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | BACKQUOTE ->
      let pos1 = current_pos lb in
      consume_token lb;
      let q = term_id lb in
      let b = binder lb in
      let b = extend_pos lb (*__FUNCTION__*) pos1 (P_Abst(fst b, snd b)) in
      extend_pos lb (*__FUNCTION__*) pos1 (P_Appl(q, b))
  | EXISTS -> (* only in Rocq *)
      let pos1 = current_pos lb in
      consume_token lb;
      let b = rocqbinder lb COMMA in
          let f = fun bin res ->
            extend_pos lb pos1 (P_Appl(
              extend_pos lb pos1 (P_Iden(extend_pos lb pos1 ([],"∃"), false)),
              extend_pos lb pos1 (P_Abst([bin], res)))) in
       (List.fold_right f (fst b) (snd b))
  | FORALL -> (* only in Rocq *)
      let pos1 = current_pos lb in
      consume_token lb;
      let b = rocqbinder lb COMMA in
      extend_pos lb (*__FUNCTION__*) pos1 (P_Prod(fst b, snd b))
  | PI ->
      let pos1 = current_pos lb in
      consume_token lb;
      let b = binder lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_Prod(fst b, snd b))
  | LAMBDA ->
      let pos1 = current_pos lb in
      consume_token lb;
      let b = binder lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_Abst(fst b, snd b))
  | FUN -> (* only in Rocq *)
      let pos1 = current_pos lb in
      consume_token lb;
      let b = rocqbinder lb THICKARROW in
      extend_pos lb (*__FUNCTION__*) pos1 (P_Abst(fst b, snd b))
  | LET ->
      let pos1 = current_pos lb in
      consume_token lb;
      let x = uid lb in
      let a = list params_tks params lb in
      begin
        match current_token lb with
        | COLON ->
            consume_token lb;
            let b = Some (term lb) in
            consume ASSIGN lb;
            let t = term lb in
            consume IN lb;
            let u = term lb in
            extend_pos lb (*__FUNCTION__*) pos1 (P_LLet(x, a, b, t, u))
        | ASSIGN ->
            let b = None in
            consume ASSIGN lb;
            let t = term lb in
            consume IN lb;
            let u = term lb in
            extend_pos lb (*__FUNCTION__*) pos1 (P_LLet(x, a, b, t, u))
        | _ ->
            expected lb "" [COLON;ASSIGN]
      end
  | _ ->
    expected lb "" [BACKQUOTE;PI;LAMBDA;LET(*;EXISTS;FORALL;FUN*)]

and aterm (lb:'token lexbuf): p_term =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
    | UID _
    | QID _
    | UID_EXPL _
    | QID_EXPL _ ->
        term_id lb
    | UNDERSCORE ->
        let pos1 = current_pos lb in
        consume_token lb;
        make_pos pos1 P_Wild
    | TYPE_TERM ->
        let pos1 = current_pos lb in
        consume_token lb;
        make_pos pos1 P_Type
    | UID_META s ->
        let pos1 = current_pos lb in
        consume_token lb;
        let i = make_pos pos1 s in
        if opt DOT lb then
          extend_pos lb (*__FUNCTION__*) pos1
            (P_Meta(i,Array.of_list (env lb)))
        else
         {i with elt=P_Meta(i,[||])}
    | UID_PATT s ->
        let pos1 = current_pos lb in
        consume_token lb;
        let i = if s = "_" then None else Some(make_pos pos1 s) in
        if opt DOT lb then
          extend_pos lb (*__FUNCTION__*) pos1
                (P_Patt(i, Some(Array.of_list (env lb))))
        else
          make_pos pos1 (P_Patt(i, None))
    | L_PAREN ->
        let pos1 = current_pos lb in
        consume_token lb;
        let t = term lb in
        consume R_PAREN lb;
        extend_pos lb (*__FUNCTION__*) pos1 (P_Wrap(t))
    | L_SQ_BRACKET ->
        let pos1 = current_pos lb in
        consume_token lb;
        let t = term lb in
        consume R_SQ_BRACKET lb;
        extend_pos lb (*__FUNCTION__*) pos1 (P_Expl(t))
    | INT n ->
        let pos1 = current_pos lb in
        consume_token lb;
        make_pos pos1 (P_NLit([],n))
    | QINT(p,n) ->
        let pos1 = current_pos lb in
        consume_token lb;
        make_pos pos1 (P_NLit(p,n))
    | STRINGLIT s ->
        let pos1 = current_pos lb in
        consume_token lb;
        make_pos pos1 (P_SLit s)
    | _ ->
      expected lb
        (string_of_tokens
           "identifier, integer or string literal, \
            term between parentheses or square brackets"
           [TYPE_TERM;UNDERSCORE]) []

and env (lb:'token lexbuf): p_term list =
  if log_enabled() then log "%s" __FUNCTION__;
  consume L_SQ_BRACKET lb;
  let res = list_with_sep term_tks term SEMICOLON lb in
  consume R_SQ_BRACKET lb;
  res

and binder (lb:'token lexbuf): p_params list * p_term =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | UID _
  | UNDERSCORE ->
      let s = param lb in
      begin
        match current_token lb with
        | UID _
        | UNDERSCORE
        | L_PAREN
        | L_SQ_BRACKET ->
            let ps = nelist params_tks params lb in
            consume COMMA lb;
            let p = [s], None, false in
            p::ps, term lb
        | COMMA ->
            consume_token lb;
            let p = [s], None, false in
            [p], term lb
        | COLON ->
            consume_token lb;
            let a = term lb in
            consume COMMA lb;
            let p = [s], Some a, false in
            [p], term lb
        | _ ->
            expected lb "" [UID"";UNDERSCORE;L_PAREN;L_SQ_BRACKET;COMMA;COLON]
      end
  | L_PAREN ->
      let ps = nelist params_tks params lb in
      consume COMMA lb;
      ps, term lb
  | L_SQ_BRACKET ->
      let ps = nelist params_tks params lb in
      consume COMMA lb;
      ps, term lb
  | _ ->
      expected lb "" [UID"";UNDERSCORE;L_PAREN;L_SQ_BRACKET]

and rocqbinder (lb:'token lexbuf) (terminator:token): p_params list * p_term =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | UID _
  | UNDERSCORE ->
      let s = param lb in
      begin
        match current_token lb with
        | UID _
        | UNDERSCORE
        | L_PAREN ->
            let ps = list params_tks params lb in
            consume terminator lb;
            let p = [s], None, false in
            p::ps, term lb
        | COLON ->
            consume_token lb;
            let a = term lb in
            consume terminator lb;
            let p = [s], Some a, false in
            [p], term lb
        | _ ->
            if current_token lb = terminator then
                begin
                    consume_token lb;
                    let p = [s], None, false in
                    [p], term lb
                end
            else
              expected lb "" [UID"";UNDERSCORE;L_PAREN;COLON;terminator]
      end
  | L_PAREN ->
      let ps = nelist params_tks params lb in
      consume terminator lb;
      ps, term lb
  | _ ->
      expected lb "" [UID"";UNDERSCORE;L_PAREN]


(* search *)

and generalize (lb:'token lexbuf): bool =
  if log_enabled() then log "%s" __FUNCTION__;
  opt GENERALIZE lb

and relation (lb:'token lexbuf): relation option =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | UID "=" -> consume_token lb; Some Exact
  | UID ">" -> consume_token lb; Some Inside
  | UID ("≥"|">=") -> consume_token lb; None
  | _ -> expected lb (tokens[">";"=";"≥";">="]) []

and where (lb:'token lexbuf): bool * relation option =
  if log_enabled() then log "%s" __FUNCTION__;
  let r = relation lb in
  let g = generalize lb in
  g,r

and asearch (lb:'token lexbuf): search =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | UID "name" ->
     consume_token lb;
     consume (UID "=") lb;
     QBase(QName (uid lb).elt)
  | TYPE_QUERY ->
      begin
        consume_token lb;
        match current_token lb with
        | UID ("≥"|">=") ->
            consume_token lb;
            let g = generalize lb in
            let t = term lb in
            QBase(QSearch(t,g,Some(QType None)))
        | _ -> expected lb (tokens["≥";">="]) []
      end
  | UID "anywhere" ->
      begin
        consume_token lb;
        match current_token lb with
        | UID ("≥"|">=") ->
            consume_token lb;
            let g = generalize lb in
            let t = term lb in
            QBase(QSearch(t,g,None))
        | _ -> expected lb (tokens["≥";">="]) []
      end
  | RULE ->
      consume_token lb;
      let r = relation lb in
      let g = generalize lb in
      let t = term lb in
      QBase(QSearch(t,g,Some(QXhs(r,None))))
  | UID "spine" ->
      consume_token lb;
      let r = relation lb in
      let g = generalize lb in
      let t = term lb in
      QBase(QSearch(t,g,Some(QType(Some(Spine r)))))
  | UID "concl" ->
      consume_token lb;
      let r = relation lb in
      let g = generalize lb in
      let t = term lb in
      QBase(QSearch(t,g,Some(QType(Some(Conclusion r)))))
  | UID "hyp" ->
      consume_token lb;
      let r = relation lb in
      let g = generalize lb in
      let t = term lb in
      QBase(QSearch(t,g,Some(QType(Some(Hypothesis r)))))
  | UID "lhs" ->
      consume_token lb;
      let r = relation lb in
      let g = generalize lb in
      let t = term lb in
      QBase(QSearch(t,g,Some(QXhs(r,Some Lhs))))
  | UID "rhs" ->
      consume_token lb;
      let r = relation lb in
      let g = generalize lb in
      let t = term lb in
      QBase(QSearch(t,g,Some(QXhs(r,Some Rhs))))
  | L_PAREN ->
      consume_token lb;
      let q = search lb in
      consume R_PAREN lb;
      q
  | _ ->
    expected lb (tokens["name";"anywhere";"rule";"lhs";"rhs";"type";"concl";
                        "hyp";"spine"]) []

and csearch (lb:'token lexbuf): search =
  if log_enabled() then log "%s" __FUNCTION__;
  let aq = asearch lb in
  let aqs = list [WITH] (prefix WITH asearch) lb in
  List.fold_left (fun x aq -> QOp(x,Intersect,aq)) aq aqs

and ssearch (lb:'token lexbuf): search =
  if log_enabled() then log "%s" __FUNCTION__;
  let cq = csearch lb in
  let cqs = list [VBAR] (prefix VBAR csearch) lb in
  List.fold_left (fun x cq -> QOp(x,Union,cq)) cq cqs

and search (lb:'token lexbuf): search =
  if log_enabled() then log "%s" __FUNCTION__;
  let q = ssearch lb in
  let qids = list [IN] (prefix IN qid_or_regexp) lb in
  List.fold_left
    (fun x qid ->
       let n = snd qid.elt in
       if String.is_string_literal n then
         QFilter(x,RegExp(String.remove_quotes n))
       else QFilter(x,Path(Format.asprintf "%a" Pretty.qident qid)))
    q qids

and alone_search (lb:'token lexbuf) : search =
 let res = search lb in
 if current_token lb = EOF then res else expected lb "" [VBAR; IN; WITH]


let command (lb:'token lexbuf): p_command =
  if current_token lb = EOF then raise End_of_file
  else
   let c = command lb in
   match current_token lb with
   | SEMICOLON -> c
   | _ -> expected lb "" [SEMICOLON]
