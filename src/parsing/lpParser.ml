open Lplib
open Common open Pos open Logger
open Syntax
open Core
open LpLexer
open Lexing
open Sedlexing
open ZipperTokenLexbuf

let log = Logger.make 'n' "pars" "parsing"
let log = log.pp

(* token management *)

let string_of_token = function
  | EOF -> "end of file"
  | ABORT -> "abort"
  | ADMIT -> "admit"
  | ADMITTED -> "admitted"
  | APPLY -> "apply"
  | ARROW -> "→"
  | AS -> "as"
  | ASSERT _ -> "assert or assertnot"
  | ASSIGN -> "≔"
  | ASSOCIATIVE -> "associative"
  | ASSUME -> "assume"
  | ASSUMPTION -> "assumption"
  | BACKQUOTE -> "`"
  | BEGIN -> "begin"
  | BUILTIN -> "builtin"
  | CHANGE -> "change"
  | COERCE_RULE -> "coerce_rule"
  | COLON -> ":"
  | COMMA -> ","
  | COMMUTATIVE -> "commutative"
  | COMPUTE -> "compute"
  | CONSTANT -> "constant"
  | DEBUG -> "debug"
  | DEBUG_FLAGS _ -> "debug flags"
  | DOT -> "."
  | END -> "end"
  | EQUIV -> "≡"
  | EVAL -> "eval"
  | EXISTS -> "exists" (* only in Rocq *)
  | FAIL -> "fail"
  | FIRST_HYP -> "first_hyp"
  | FLAG -> "flag"
  | FLOAT _ -> "float"
  | FOCUS -> "focus"
  | FORALL -> "forall" (* only in Rocq *)
  | FUN -> "fun"       (* only in Rocq *)
  | GENERALIZE -> "generalize"
  | HAVE -> "have"
  | HOOK_ARROW -> "↪"
  | IN -> "in"
  | INDUCTION -> "induction"
  | INDUCTIVE -> "inductive"
  | INFIX -> "infix"
  | INJECTIVE -> "injective"
  | INT _ -> "integer"
  | LAMBDA -> "λ"
  | LET -> "let"
  | L_CU_BRACKET -> "{"
  | L_PAREN -> "("
  | L_SQ_BRACKET -> "["
  | NOTATION -> "notation"
  | OPAQUE -> "opaque"
  | OPEN -> "open"
  | ORELSE -> "orelse"
  | PI -> "Π"
  | POSTFIX -> "postfix"
  | PREFIX -> "prefix"
  | PRINT -> "print"
  | PRIVATE -> "private"
  | PROOFTERM -> "proofterm"
  | PROTECTED -> "protected"
  | PROVER -> "prover"
  | PROVER_TIMEOUT -> "prover_timeout"
  | QID _ -> "qualified identifier"
  | QID_EXPL _ -> "@-prefixed qualified identifier"
  | QINT _ -> "qualified integer"
  | QUANTIFIER -> "quantifier"
  | REFINE -> "refine"
  | REFLEXIVITY -> "reflexivity"
  | REMOVE -> "remove"
  | REPEAT -> "repeat"
  | REQUIRE -> "require"
  | REWRITE -> "rewrite"
  | RULE -> "rule"
  | R_CU_BRACKET -> "}"
  | R_PAREN -> ")"
  | R_SQ_BRACKET -> "]"
  | SEARCH -> "search"
  | SEQUENTIAL -> "sequential"
  | SEMICOLON -> ";"
  | SET -> "set"
  | SIDE _ -> "left or right"
  | SIMPLIFY -> "simplify"
  | SOLVE -> "solve"
  | STRINGLIT _ -> "string literal"
  | SWITCH false -> "off"
  | SWITCH true -> "on or off"
  | SYMBOL -> "symbol"
  | SYMMETRY -> "symmetry"
  | THICKARROW -> "=>" (* only in Rocq *)
  | TRY -> "try"
  | TURNSTILE -> "⊢"
  | TYPE_QUERY -> "type"
  | TYPE_TERM -> "TYPE"
  | UID _ -> "non-qualified identifier"
  | UID_EXPL _ -> "@-prefixed non-qualified identifier"
  | UID_META _ -> "?-prefixed metavariable number"
  | UID_PATT _ -> "$-prefixed non-qualified identifier"
  | UNDERSCORE -> "_"
  | UNIF_RULE -> "unif_rule"
  | VBAR -> "|"
  | VERBOSE -> "verbose"
  | WHY3 -> "why3"
  | WITH -> "with"

let pp_token ppf t = Base.string ppf (string_of_token t)

let expected (msg:string) (tokens:token list) lb : 'a =
  if msg <> "" then syntax_error (current_pos lb) ("Expected: "^msg^".")
  else
    match tokens with
    | [] -> assert false
    | t::ts ->
      let soft t = String.add_quotes (string_of_token t) in
      syntax_error (current_pos lb)
        (List.fold_left (fun s t -> s^", "^soft t) ("Expected: "^soft t) ts
        ^".")

(* building positions and terms *)

let extend_pos lb (*s:string*) (lps:position * position) : 'a -> 'a loc =
  let p1 = fst lps and p2 = fst (current_pos lb) in
  let p2 =
    if p2.pos_cnum > p2.pos_bol then
      {p2 with pos_cnum = p2.pos_cnum - 1}
    else p2
  in
  (*if log_enabled() then
    log "extend_pos lb %s %a -> %a" s Pos.pp_lexing lps Pos.pp_lexing lps2;*)
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

let list (elt:'token lexbuf -> 'a) (lb:'token lexbuf): 'a list =
  if log_enabled() then log "%s" __FUNCTION__;
  let acc = ref [] in
  (try
    while true do acc := succeed_or_reset_stream elt lb :: !acc done
   with SyntaxError _ -> ());
  List.rev !acc

let nelist (elt:'token lexbuf -> 'a) (lb:'token lexbuf): 'a list =
  if log_enabled() then log "%s" __FUNCTION__;
  let x = elt lb in
  x :: list elt lb

let consume (token:token) (lb:'token lexbuf): unit =
  if current_token lb = token then consume_token lb
  else expected "" [token] lb

let prefix (token:token) (elt:'token lexbuf -> 'a) (lb:'token lexbuf): 'a =
  consume token lb; elt lb

(* parsing functions *)

let consume_STRINGLIT (lb:'token lexbuf): string =
  match current_token lb with
  | STRINGLIT s ->
      consume_token lb;
      s
  | _ ->
      expected "" [STRINGLIT""] lb

let consume_SWITCH (lb:'token lexbuf): bool =
  match current_token lb with
  | SWITCH b ->
      consume_token lb;
      b
  | _ ->
      expected "" [SWITCH true] lb

let consume_INT (lb:'token lexbuf): string =
  match current_token lb with
  | INT s ->
      consume_token lb;
      s
  | _ ->
      expected "" [INT""] lb

let consume_DEBUG_FLAGS (lb:'token lexbuf): bool * string =
  match current_token lb with
  | DEBUG_FLAGS(b,s) ->
      consume_token lb;
      b,s
  | _ ->
      expected "" [DEBUG_FLAGS(true,"")] lb

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
      expected "" [UID"";QID[]] lb

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
      expected "" [UID"";QID[];STRINGLIT""] lb

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
      expected "" [UID_EXPL"";QID_EXPL[]] lb

let uid (lb:'token lexbuf): string loc =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | UID s ->
      let pos1 = current_pos lb in
      consume_token lb;
      make_pos pos1 s
  | _ ->
      expected "" [UID""] lb

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
      expected "non-qualified identifier or \"_\"" [UID"";UNDERSCORE] lb

let int (lb:'token lexbuf): string =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | INT s ->
      consume_token lb;
      s
  | _ ->
      expected "integer" [INT""] lb

let float_or_int (lb:'token lexbuf): string =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | INT s
  | FLOAT s ->
      consume_token lb;
      s
  | _ ->
      expected "integer or float" [INT"";FLOAT""] lb

let path (lb:'token lexbuf): string list loc =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | QID p ->
      let pos1 = current_pos lb in
      consume_token lb;
      make_pos pos1 (List.rev p)
  | _ ->
      expected "" [QID[]] lb

let qid_or_rule (lb:'token lexbuf): (string list * string) loc =
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
  | UNIF_RULE ->
      let pos1 = current_pos lb in
      consume_token lb;
      make_pos pos1 ([], Unif_rule.equiv.sym_name)
  | COERCE_RULE ->
      let pos1 = current_pos lb in
      consume_token lb;
      make_pos pos1 ([], Coercion.coerce.sym_name)
  | _ ->
      expected "" [UID"";QID[];STRINGLIT"";UNIF_RULE;COERCE_RULE] lb

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
      expected "" [UID"";QID[];UID_EXPL"";QID_EXPL[]] lb

(* commands *)

let rec command pos1 (p_sym_mod:p_modifier list) (lb:'token lexbuf) :
 p_command =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | SIDE _
  | ASSOCIATIVE
  | COMMUTATIVE
  | CONSTANT
  | INJECTIVE
  | SEQUENTIAL
  | PRIVATE
  | OPAQUE
  | PROTECTED ->
      assert (p_sym_mod = []);
      let pos1 = current_pos lb in
      command pos1 (nelist modifier lb) lb
  (* qid *)
  | UID _
  | QID _ ->
      begin
        match p_sym_mod with
        | [{elt=P_opaq;_}] ->
            let i = qid lb in
            extend_pos lb (*__FUNCTION__*) pos1 (P_opaque i)
        | [] ->
            expected "command keyword missing" [] lb
        | {elt=P_opaq;_}::{pos;_}::_ ->
            expected "an opaque command must be followed by an identifier" []
             lb
        | _ ->
            expected "" [SYMBOL] lb
      end
  | REQUIRE ->
      if p_sym_mod <> [] then expected "" [SYMBOL] lb; (*or modifiers*)
      let pos1 = current_pos lb in
      consume_token lb;
      begin
        match current_token lb with
        | OPEN ->
            consume_token lb;
            let ps = nelist path lb in
            extend_pos lb (*__FUNCTION__*) pos1 (P_require(Some false,ps))
        | PRIVATE ->
            consume_token lb;
            begin
              match current_token lb with
              | OPEN -> consume_token lb
              | _ -> expected "" [OPEN] lb
            end;
            let ps = nelist path lb in
            extend_pos lb (*__FUNCTION__*) pos1 (P_require(Some true,ps))
        | _ ->
            let ps = nelist path lb in
            begin
              match current_token lb with
              | AS ->
                  let p =
                    match ps with
                    | [p] -> p
                    | _ -> expected "a single module before \"as\"" [] lb
                  in
                  consume_token lb;
                  let i = uid lb in
                  extend_pos lb (*__FUNCTION__*) pos1 (P_require_as(p,i))
              | _ ->
                  extend_pos lb (*__FUNCTION__*) pos1 (P_require(None,ps))
            end
      end
  | OPEN ->
      let prv =
        match p_sym_mod with
        | [] -> false
        | {elt=P_expo Term.Privat;_}::_ -> true
        | _ -> expected "" [SYMBOL] lb
      in
      let pos1 = current_pos lb in
      consume_token lb;
      let l = list path lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_open(prv,l))
  | SYMBOL ->
      let pos1 = current_pos lb in
      consume_token lb;
      let p_sym_nam = uid lb in
      let p_sym_arg = list params lb in
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
                    {p_sym_mod; p_sym_nam; p_sym_arg; p_sym_typ;
                     p_sym_trm=None; p_sym_def; p_sym_prf}
                  in extend_pos lb (*__FUNCTION__*) pos1 (P_symbol(sym))
              | ASSIGN ->
                  consume_token lb;
                  let p_sym_trm, p_sym_prf = term_proof lb in
                  let p_sym_def = true in
                  let sym =
                    {p_sym_mod; p_sym_nam; p_sym_arg; p_sym_typ;
                     p_sym_trm; p_sym_def; p_sym_prf}
                  in extend_pos lb (*__FUNCTION__*) pos1 (P_symbol(sym))
              | SEMICOLON ->
                  let p_sym_trm = None in
                  let p_sym_def = false in
                  let p_sym_prf = None in
                  let sym =
                    {p_sym_mod; p_sym_nam; p_sym_arg; p_sym_typ;
                     p_sym_trm; p_sym_def; p_sym_prf}
                  in extend_pos lb (*__FUNCTION__*) pos1 (P_symbol(sym))
              | _ ->
                  expected "" [BEGIN;ASSIGN] lb
            end
        | ASSIGN ->
            consume_token lb;
            let p_sym_trm, p_sym_prf = term_proof lb in
            let p_sym_def = true in
            let p_sym_typ = None in
            let sym =
              {p_sym_mod; p_sym_nam; p_sym_arg; p_sym_typ;
               p_sym_trm; p_sym_def; p_sym_prf}
            in extend_pos lb (*__FUNCTION__*) pos1 (P_symbol(sym))
        | _ ->
            expected "" [COLON;ASSIGN] lb
      end
  | L_PAREN
  | L_SQ_BRACKET ->
      let pos1 = current_pos lb in
      let xs = nelist params lb in
      consume INDUCTIVE lb;
      let i = inductive lb in
      let is = list (prefix WITH inductive) lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_inductive(p_sym_mod,xs,i::is))
  | INDUCTIVE ->
      let pos1 = current_pos lb in
      consume_token lb;
      let i = inductive lb in
      let is = list (prefix WITH inductive) lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_inductive(p_sym_mod,[],i::is))
  | RULE ->
      if p_sym_mod <> [] then expected "" [SYMBOL] lb; (*or modifiers*)
      let pos1 = current_pos lb in
      consume_token lb;
      let r = rule lb in
      let rs = list (prefix WITH rule) lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_rules(r::rs))
  | UNIF_RULE ->
      if p_sym_mod <> [] then expected "" [SYMBOL] lb; (*or modifiers*)
      let pos1 = current_pos lb in
      consume_token lb;
      let e = equation lb in
      consume HOOK_ARROW lb;
      consume L_SQ_BRACKET lb;
      let eq1 = equation lb in
      let eqs = list (prefix SEMICOLON equation) lb in
      let es = eq1::eqs in
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
      if p_sym_mod <> [] then expected "" [SYMBOL] lb; (*or modifiers*)
      let pos1 = current_pos lb in
      consume_token lb;
      let r = rule lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_coercion r)
  | BUILTIN ->
      if p_sym_mod <> [] then expected "" [SYMBOL] lb; (*or modifiers*)
      let pos1 = current_pos lb in
      consume_token lb;
      begin
        match current_token lb with
        | STRINGLIT s ->
            consume_token lb;
            consume ASSIGN lb;
            let s = String.remove_quotes s and i = qid lb in
            extend_pos lb (*__FUNCTION__*) pos1 (P_builtin(s,i))
        | _ ->
            expected "" [STRINGLIT""] lb
      end
  | NOTATION ->
      if p_sym_mod <> [] then expected "" [SYMBOL] lb; (*or modifiers*)
      let pos1 = current_pos lb in
      consume_token lb;
      let i = qid lb in
      let n = notation lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_notation(i,n))
  | _ ->
      if p_sym_mod <> [] then expected "" [SYMBOL] lb; (*or modifiers*)
      let pos1 = current_pos lb in
      let q = query lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_query(q))

and inductive (lb:'token lexbuf): p_inductive =
  let pos0 = current_pos lb in
  let i = uid lb in
  let pos1 = current_pos lb in
  let ps = list params lb in
  consume COLON lb;
  let t = term lb in
  let pos2 = current_pos lb in
  let t = make_prod lb (fst pos1) ps t (snd pos2) in
  consume ASSIGN lb;
  begin
    match current_token lb with
    | UID _ ->
        let c = constructor lb in
        let cs = list (prefix VBAR constructor) lb in
        let l = c::cs in
        extend_pos lb (*__FUNCTION__*) pos0 (i,t,l)
    | VBAR ->
        let l = nelist (prefix VBAR constructor) lb in
        extend_pos lb (*__FUNCTION__*) pos0 (i,t,l)
    | SEMICOLON ->
        let l = [] in
        extend_pos lb (*__FUNCTION__*) pos0 (i,t,l)
    | _ ->
        expected "identifier" [] lb
    end

and constructor (lb:'token lexbuf): p_ident * p_term =
  let i = uid lb in
  let pos1 = current_pos lb in
  let ps = list params lb in
  consume COLON lb;
  let t = term lb in
  i, make_prod lb (fst pos1) ps t (snd (current_pos lb))

and modifier (lb:'token lexbuf): p_modifier =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | SIDE d ->
      let pos1 = current_pos lb in
      consume_token lb;
      begin
        match current_token lb with
        | ASSOCIATIVE ->
            consume_token lb;
            extend_pos lb (*__FUNCTION__*) pos1
              (P_prop (Term.Assoc((d = Pratter.Left))))
        | _ ->
            expected "" [ASSOCIATIVE] lb
      end
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
  | SEQUENTIAL ->
      let pos1 = current_pos lb in
      consume_token lb;
      extend_pos lb (*__FUNCTION__*) pos1 (P_mstrat Term.Sequen)
  | _ ->
      exposition lb

and exposition (lb:'token lexbuf): p_modifier =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | PRIVATE ->
      let pos1 = current_pos lb in
      consume_token lb;
      extend_pos lb (*__FUNCTION__*) pos1 (P_expo Term.Privat)
  | PROTECTED ->
      let pos1 = current_pos lb in
      consume_token lb;
      extend_pos lb (*__FUNCTION__*) pos1 (P_expo Term.Protec)
  | _ ->
      expected "" [PRIVATE;PROTECTED] lb

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
        | _ ->
            let p = float_or_int lb in
            Term.Infix(Pratter.Neither, p)
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
      expected "" [INFIX;POSTFIX;PREFIX;QUANTIFIER] lb

and rule (lb:'token lexbuf): (p_term * p_term) loc =
  if log_enabled() then log "%s" __FUNCTION__;
  let pos1 = current_pos lb in
  let l = term lb in
  consume HOOK_ARROW lb;
  let r = term lb in
  extend_pos lb (*__FUNCTION__*) pos1 (l, r)

and equation (lb:'token lexbuf): p_term * p_term =
  if log_enabled() then log "%s" __FUNCTION__;
  let l = term lb in
  consume EQUIV lb;
  let r = term lb in
  (l, r)

(* queries *)

and query (lb:'token lexbuf): p_query =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | ASSERT b ->
      let pos1 = current_pos lb in
      consume_token lb;
      let ps = list params lb in
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
            expected "" [COLON;EQUIV] lb
      end
  | COMPUTE ->
      let pos1 = current_pos lb in
      consume_token lb;
      let t = term lb in
      extend_pos lb (*__FUNCTION__*) pos1
        (P_query_normalize(t, {strategy=SNF; steps=None}))
  | PRINT ->
      let pos1 = current_pos lb in
      consume_token lb;
      begin
        match current_token lb with
        | SEMICOLON ->
            extend_pos lb (*__FUNCTION__*) pos1 (P_query_print None)
        | _ ->
            let i = qid_or_rule lb in
            extend_pos lb (*__FUNCTION__*) pos1 (P_query_print (Some i))
      end
  | PROOFTERM ->
      let pos1 = current_pos lb in
      consume_token lb;
      extend_pos lb (*__FUNCTION__*) pos1 P_query_proofterm
  | DEBUG ->
      let pos1 = current_pos lb in
      consume_token lb;
      begin
        match current_token lb with
        | SEMICOLON ->
            extend_pos lb (*__FUNCTION__*) pos1 (P_query_debug(true,""))
        | _ ->
            let b,s = consume_DEBUG_FLAGS lb in
            extend_pos lb (*__FUNCTION__*) pos1 (P_query_debug(b,s))
      end
  | FLAG ->
      let pos1 = current_pos lb in
      consume_token lb;
      begin
        match current_token lb with
        | SEMICOLON ->
            extend_pos lb (*__FUNCTION__*) pos1 (P_query_flag("",true))
        | _ ->
          let s = String.remove_quotes (consume_STRINGLIT lb) in
          let b = consume_SWITCH lb in
          extend_pos lb (*__FUNCTION__*) pos1 (P_query_flag(s,b))
      end
  | PROVER ->
      let pos1 = current_pos lb in
      consume_token lb;
      let s = String.remove_quotes (consume_STRINGLIT lb) in
      extend_pos lb (*__FUNCTION__*) pos1 (P_query_prover(s))
  | PROVER_TIMEOUT ->
      let pos1 = current_pos lb in
      consume_token lb;
      let n = consume_INT lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_query_prover_timeout n)
  | VERBOSE ->
      let pos1 = current_pos lb in
      consume_token lb;
      let n = consume_INT lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_query_verbose n)
  | TYPE_QUERY ->
      let pos1 = current_pos lb in
      consume_token lb;
      let t = term lb in
      extend_pos lb (*__FUNCTION__*) pos1
        (P_query_infer(t, {strategy=NONE; steps=None}))
  | SEARCH ->
      let pos1 = current_pos lb in
      consume_token lb;
      let q = search lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_query_search q)
  | _ ->
      expected "query" [] lb

and term_proof (lb:'token lexbuf):
 p_term option * (p_proof * p_proof_end) option =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | BEGIN ->
      consume_token lb;
      let p = proof lb in
      None, Some p
  | _ ->
      let t = term lb in
      begin
        match current_token lb with
        | BEGIN ->
            consume_token lb;
            let p = proof lb in
            Some t, Some p
        | _ ->
            Some t, None
      end

(* proofs *)

and proof (lb:'token lexbuf): p_proof * p_proof_end =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | L_CU_BRACKET ->
      let l = nelist subproof lb in
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
  | APPLY
  | ASSUME
  | CHANGE
  | EVAL
  | FAIL
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
      expected "subproof, tactic or query" [] lb

and subproof (lb:'token lexbuf): p_proofstep list =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | L_CU_BRACKET ->
      consume_token lb;
      let l = steps lb in
      consume R_CU_BRACKET lb;
      l
  | _ ->
      expected "" [L_CU_BRACKET] lb

and steps (lb:'token lexbuf): p_proofstep list =
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
  | VERBOSE
  (*tactics*)
  | ADMIT
  | APPLY
  | ASSUME
  | ASSUMPTION
  | CHANGE
  | EVAL
  | FAIL
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
      let a = step lb in
      let acc = list (prefix SEMICOLON step) lb in
      if current_token lb = SEMICOLON then consume_token lb;
      a::acc
  | END
  | ABORT
  | ADMITTED
  | R_CU_BRACKET ->
      []
  | _ ->
      expected "tactic or query" [] lb

and step (lb:'token lexbuf): p_proofstep =
  if log_enabled() then log "%s" __FUNCTION__;
  let t = tactic lb in
  let l = list subproof lb in
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
      expected "" [ABORT;ADMITTED;END] lb

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
  | APPLY ->
      let pos1 = current_pos lb in
      consume_token lb;
      let t = term lb in
      extend_pos lb (*__FUNCTION__*) pos1 (P_tac_apply t)
  | ASSUME ->
      let pos1 = current_pos lb in
      consume_token lb;
      let xs = nelist param lb in
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
      begin
        match current_token lb with
        | INT n ->
            consume_token lb;
            extend_pos lb (*__FUNCTION__*) pos1 (P_tac_focus n)
        | _ -> expected "" [INT ""] lb
      end
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
      let xs = nelist uid lb in
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
            begin
              match current_token lb with
              | DOT ->
                  consume_token lb;
                  let p = rwpatt_bracket lb in
                  let t = term lb in
                  let b = d <> Pratter.Left in
                  extend_pos lb (*__FUNCTION__*) pos1
                   (P_tac_rewrite(b,Some p,t))
              | _ ->
                  let t = term lb in
                  let b = d <> Pratter.Left in
                  extend_pos lb (*__FUNCTION__*) pos1
                   (P_tac_rewrite(b,None,t))
            end
        | DOT ->
            consume_token lb;
            let p = rwpatt_bracket lb in
            let t = term lb in
            extend_pos lb (*__FUNCTION__*) pos1 (P_tac_rewrite(true,Some p,t))
        | _ ->
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
            begin
              match current_token lb with
              | SWITCH false ->
                  consume_token lb;
                  extend_pos lb (*__FUNCTION__*) pos1
                   (P_tac_simpl SimpBetaOnly)
              | _ -> expected "" [SWITCH false] lb
            end
        | _ ->
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
            make_pos pos1 (P_tac_why3 None)
      end
  | _ ->
      expected "tactic" [] lb

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
            begin
              match current_token lb with
              | IN ->
                  consume_token lb;
                  let t3 = term lb in
                  let x = ident_of_term pos1 t2 in
                  extend_pos lb (*__FUNCTION__*) pos1
                    (Rw_TermInIdInTerm(t1,(x,t3)))
              | _ ->
                  let x = ident_of_term pos1 t1 in
                  extend_pos lb (*__FUNCTION__*) pos1 (Rw_IdInTerm(x,t2))
            end
        | AS ->
            consume_token lb;
            let t2 = term lb in
            begin
              match current_token lb with
              | IN ->
                  consume_token lb;
                  let t3 = term lb in
                  let x = ident_of_term pos1 t2 in
                  extend_pos lb (*__FUNCTION__*) pos1
                    (Rw_TermAsIdInTerm(t1,(x,t3)))
              | _ ->
                  expected "" [IN] lb
            end
        | _ ->
            extend_pos lb (*__FUNCTION__*) pos1 (Rw_Term(t1))
      end
  | IN ->
      let pos1 = current_pos lb in
      consume_token lb;
      let t1 = term lb in
      begin
        match current_token lb with
        | IN ->
            consume_token lb;
            let t2 = term lb in
            let x = ident_of_term pos1 t1 in
            extend_pos lb (*__FUNCTION__*) pos1 (Rw_InIdInTerm(x,t2))
        | _ ->
            extend_pos lb (*__FUNCTION__*) pos1 (Rw_InTerm(t1))
      end
  | _ ->
      expected "term or keyword \"in\"" [] lb

and rwpatt_bracket (lb:'token lexbuf): p_rwpatt =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | L_SQ_BRACKET ->
      consume_token lb;
      let p = rwpatt_content lb in
      consume R_SQ_BRACKET lb; (*add info on opening bracket*)
      p
  | _ ->
      expected "" [L_SQ_BRACKET] lb

and rwpatt (lb:'token lexbuf): p_rwpatt =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | DOT ->
      consume_token lb;
      rwpatt_bracket lb
  | _ ->
      expected "" [DOT] lb

(* terms *)

and params (lb:'token lexbuf): p_params =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | L_PAREN ->
      consume_token lb;
      let ps = nelist param lb in
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
            expected "" [COLON;R_PAREN] lb
      end
  | L_SQ_BRACKET ->
      consume_token lb;
      let ps = nelist param lb in
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
            expected "" [COLON;R_SQ_BRACKET] lb
      end
  | _ ->
      let x = param lb in
      [x], None, false

and term (lb:'token lexbuf): p_term =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  (* bterm *)
  | BACKQUOTE
  | EXISTS (* not in Rocq *)
  | FORALL (* not in Rocq *)
  | FUN    (* not in Rocq *)
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
      expected "term" [] lb

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
      let a = list params lb in
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
        | _ ->
            let b = None in
            consume ASSIGN lb;
            let t = term lb in
            consume IN lb;
            let u = term lb in
            extend_pos lb (*__FUNCTION__*) pos1 (P_LLet(x, a, b, t, u))
      end
  | _ ->
      expected "" [BACKQUOTE;PI;LAMBDA;LET] lb

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
        begin
          match current_token lb with
          | DOT ->
              consume_token lb;
              extend_pos lb (*__FUNCTION__*) pos1
                (P_Meta(i,Array.of_list (env lb)))
          | _ ->
              {i with elt=P_Meta(i,[||])}
        end
    | UID_PATT s ->
        let pos1 = current_pos lb in
        consume_token lb;
        let i =
          if s = "_" then None else Some(make_pos pos1 s) in
        begin
          match current_token lb with
          | DOT ->
              consume_token lb;
              extend_pos lb (*__FUNCTION__*) pos1
                (P_Patt(i, Some(Array.of_list (env lb))))
          | _ ->
              make_pos pos1 (P_Patt(i, None))
        end
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
        expected "identifier, \"_\", or term between parentheses or square \
                  brackets" [] lb

and env (lb:'token lexbuf): p_term list =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | L_SQ_BRACKET ->
      consume_token lb;
      begin
        match current_token lb with
        | R_SQ_BRACKET ->
            consume_token lb;
            []
        | _ ->
            let t = term lb in
            let ts = list (prefix SEMICOLON term) lb in
            consume R_SQ_BRACKET lb;
            t::ts
      end
  | _ ->
      expected "" [L_SQ_BRACKET] lb

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
            let ps = nelist params lb in
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
            expected "parameter list"
              [UID"";UNDERSCORE;L_PAREN;L_SQ_BRACKET;COMMA]
              lb
      end
  | L_PAREN ->
      let ps = nelist params lb in
      begin
        match current_token lb with
        | COMMA ->
            consume_token lb;
            ps, term lb
        | _ ->
            expected "" [COMMA] lb
      end
  | L_SQ_BRACKET ->
      let ps = nelist params lb in
      begin
        match current_token lb with
        | COMMA ->
            consume_token lb;
            ps, term lb
        | _ ->
            expected "" [COMMA] lb
      end
  | _ ->
      expected "" [UID"";UNDERSCORE;L_PAREN;L_SQ_BRACKET] lb

and rocqbinder (lb:'token lexbuf) terminator : p_params list * p_term =
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
            let ps = list params lb in
            consume terminator lb;
            let p = [s], None, false in
            p::ps, term lb
        | COLON ->
            consume_token lb;
            let a = term lb in
            consume terminator lb;
            let p = [s], Some a, false in
            [p], term lb
        (* | terminator *)
        | _ ->
            if current_token lb = terminator then
                begin
                    consume_token lb;
                    let p = [s], None, false in
                    [p], term lb
                end
            else
            expected "parameter list"
              [UID"";UNDERSCORE;L_PAREN;terminator] lb
      end
  | L_PAREN ->
      let ps = nelist params lb in
      begin
        match current_token lb with
        | _ ->
            if current_token lb = terminator then
                begin
                    consume_token lb;
                    ps, term lb
                end
            else
            expected "" [terminator] lb
      end
  | _ ->
      expected "" [UID"";UNDERSCORE;L_PAREN;] lb


(* search *)

and generalize (lb:'token lexbuf): bool =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | GENERALIZE -> consume_token lb; true
  | _ -> false

and relation (lb:'token lexbuf): relation option =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | UID "=" -> consume_token lb; Some Exact
  | UID ">" -> consume_token lb; Some Inside
  | UID ("≥"|">=") -> consume_token lb; None
  | _ -> expected "\">\", \"=\", \"≥\",\">=\"" [] lb

and where (lb:'token lexbuf): bool * relation option =
  if log_enabled() then log "%s" __FUNCTION__;
  let r = relation lb in
  let g = generalize lb in
  g,r

and asearch (lb:'token lexbuf): search =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token lb with
  | UID "name" ->
      begin
        consume_token lb;
        match current_token lb with
        | UID "=" ->
            consume_token lb;
            QBase(QName (uid lb).elt)
        | _ -> expected "\"=\"" [] lb
      end
  | TYPE_QUERY ->
      begin
        consume_token lb;
        match current_token lb with
        | UID ("≥"|">=") ->
            consume_token lb;
            let g = generalize lb in
            let t = term lb in
            QBase(QSearch(t,g,Some(QType None)))
        | _ -> expected "\"≥\",\">=\"" [] lb
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
        | _ -> expected "\"≥\",\">=\"" [] lb
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
      expected "name, anywhere, rule, lhs, rhs, type, concl, hyp, spine" [] lb

and csearch (lb:'token lexbuf): search =
  if log_enabled() then log "%s" __FUNCTION__;
  let aq = asearch lb in
  match current_token lb with
  | WITH ->
      let aqs = nelist (prefix WITH asearch) lb in
      List.fold_left (fun x aq -> QOp(x,Intersect,aq)) aq aqs
  | _ ->
      aq

and ssearch (lb:'token lexbuf): search =
  if log_enabled() then log "%s" __FUNCTION__;
  let cq = csearch lb in
  match current_token lb with
  | VBAR ->
      let cqs = nelist (prefix VBAR csearch) lb in
      List.fold_left (fun x cq -> QOp(x,Union,cq)) cq cqs
  | _ ->
      cq

and search (lb:'token lexbuf): search =
  if log_enabled() then log "%s" __FUNCTION__;
  let q = ssearch lb in
  let qids = list (prefix IN qid_or_regexp) lb in
  List.fold_left
    (fun x qid ->
       let n = snd qid.elt in
       if String.is_string_literal n then
         QFilter(x,RegExp(String.remove_quotes n))
       else QFilter(x,Path(Format.asprintf "%a" Pretty.qident qid)))
    q qids

and alone_search (lb:'token lexbuf) : search =
 let res = search lb in
 if current_token lb = EOF then res else expected "" [VBAR; IN; WITH] lb


let command (lb:'token lexbuf): p_command =
  if log_enabled() then log "------------------- start reading command";
  if current_token lb = EOF then raise End_of_file
  else
    let c = command (Lexing.dummy_pos,Lexing.dummy_pos) [] lb in
    match current_token lb with
    | SEMICOLON -> c
    | _ -> expected "" [SEMICOLON] lb
