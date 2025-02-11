open Lplib
open Common open Pos open Logger
open Syntax
open Core
open LpLexer
open Lexing
open Sedlexing

let log = Logger.make 'n' "pars" "parsing"
let log = log.pp

(* token management *)

(* error messages *)

let string_of_token = function
  | EOF -> "end of file"
  | ABORT -> "abort"
  | ADMIT -> "admit"
  | ADMITTED -> "admitted"
  | APPLY -> "apply"
  | AS -> "as"
  | ASSERT _ -> "assert or assertnot"
  | ASSOCIATIVE -> "associative"
  | ASSUME -> "assume"
  | BEGIN -> "begin"
  | BUILTIN -> "builtin"
  | COERCE_RULE -> "coerce_rule"
  | COMMUTATIVE -> "commutative"
  | COMPUTE -> "compute"
  | CONSTANT -> "constant"
  | DEBUG -> "debug"
  | END -> "end"
  | FAIL -> "fail"
  | FLAG -> "flag"
  | GENERALIZE -> "generalize"
  | HAVE -> "have"
  | IN -> "in"
  | INDUCTION -> "induction"
  | INDUCTIVE -> "inductive"
  | INFIX -> "infix"
  | INJECTIVE -> "injective"
  | INT _ -> "integer"
  | LET -> "let"
  | NOTATION -> "notation"
  | OPAQUE -> "opaque"
  | OPEN -> "open"
  | POSTFIX -> "postfix"
  | PREFIX -> "prefix"
  | PRINT -> "print"
  | PRIVATE -> "private"
  | PROOFTERM -> "proofterm"
  | PROTECTED -> "protected"
  | PROVER -> "prover"
  | PROVER_TIMEOUT -> "prover_timeout"
  | QUANTIFIER -> "quantifier"
  | REFINE -> "refine"
  | REFLEXIVITY -> "reflexivity"
  | REMOVE -> "remove"
  | REQUIRE -> "require"
  | REWRITE -> "rewrite"
  | RULE -> "rule"
  | SEARCH -> "search"
  | SEQUENTIAL -> "sequential"
  | SET -> "set"
  | SIMPLIFY -> "simplify"
  | SOLVE -> "solve"
  | SYMBOL -> "symbol"
  | SYMMETRY -> "symmetry"
  | TRY -> "try"
  | TYPE_QUERY -> "type"
  | TYPE_TERM -> "TYPE"
  | UNIF_RULE -> "unif_rule"
  | VERBOSE -> "verbose"
  | WHY3 -> "why3"
  | WITH -> "with"
  | DEBUG_FLAGS _ -> "debug flags"
  | FLOAT _ -> "float"
  | SIDE _ -> "left or right"
  | STRINGLIT _ -> "string literal"
  | SWITCH _ -> "on or off"
  | ASSIGN -> "≔"
  | ARROW -> "→"
  | BACKQUOTE -> "`"
  | COMMA -> ","
  | COLON -> ":"
  | DOT -> "."
  | EQUIV -> "≡"
  | HOOK_ARROW -> "↪"
  | LAMBDA -> "λ"
  | L_CU_BRACKET -> "{"
  | L_PAREN -> "("
  | L_SQ_BRACKET -> "["
  | PI -> "Π"
  | R_CU_BRACKET -> "}"
  | R_PAREN -> ")"
  | R_SQ_BRACKET -> "]"
  | SEMICOLON -> ";"
  | TURNSTILE -> "⊢"
  | VBAR -> "|"
  | UNDERSCORE -> "_"
  | UID _ -> "non-qualified identifier"
  | UID_EXPL _ -> "@-prefixed non-qualified identifier"
  | UID_META _ -> "?-prefixed metavariable number"
  | UID_PATT _ -> "$-prefixed non-qualified identifier"
  | QID _ -> "qualified identifier"
  | QID_EXPL _ -> "@-prefixed qualified identifier"

let pp_token ppf t = Base.string ppf (string_of_token t)

let the_current_token : (token * position * position) Stdlib.ref =
  Stdlib.ref (EOF, dummy_pos, dummy_pos)

let current_token() : token =
  let (t,_,_) = !the_current_token in
  if log_enabled() then log "current_token: %a" pp_token t;
  t

let current_pos() : position * position =
  let (_,p1,p2) = !the_current_token in (p1,p2)

let expected (msg:string) (tokens:token list): 'a =
  if msg <> "" then syntax_error (current_pos()) ("Expected: "^msg^".")
  else
    match tokens with
    | [] -> assert false
    | t::ts ->
      let soft = string_of_token in
      syntax_error (current_pos())
        (List.fold_left (fun s t -> s^", "^soft t) ("Expected: "^soft t) ts
        ^".")

let consume_token (lb:lexbuf) : unit =
  the_current_token := token lb ();
  if log_enabled() then log "read new token"

(* building positions and terms *)

let make_pos (lps:position * position): 'a -> 'a loc =
  Pos.make_pos (fst lps, snd (current_pos()))

let qid_of_path (lps: position * position):
      string list -> (string list * string) loc = function
  | [] -> assert false
  | id::mp -> make_pos lps (List.rev mp, id)

let make_abst (pos1:position) (ps:p_params list) (t:p_term) (pos2:position)
    :p_term =
  if ps = [] then t else make_pos (pos1,pos2) (P_Abst(ps,t))

let make_prod (pos1:position) (ps:p_params list) (t:p_term) (pos2:position)
    :p_term =
  if ps = [] then t else make_pos (pos1,pos2) (P_Prod(ps,t))

let ident_of_term pos1 {elt; _} =
  match elt with
  | P_Iden({elt=([], x); pos}, _) -> Pos.make pos x
  | _ -> LpLexer.syntax_error pos1 "not an identifier."

(* generic parsing functions *)

let list (elt:lexbuf -> 'a) (lb:lexbuf): 'a list =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  let acc = ref [] in
  (try while true do acc := elt lb :: !acc done with SyntaxError _ -> ());
  List.rev !acc

let nelist (elt:lexbuf -> 'a) (lb:lexbuf): 'a list =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  let x = elt lb in
  x :: list elt lb

let consume (token:token) (lb:lexbuf): unit =
  if current_token() = token then consume_token lb
  else expected "" [token]

let prefix (token:token) (elt:lexbuf -> 'a) (lb:lexbuf): 'a =
  consume token lb; elt lb

let alone (entry:lexbuf -> 'a) (lb:lexbuf): 'a =
  let x = entry lb in if current_token() != EOF then expected "" [EOF] else x

(* parsing functions *)

let consume_STRINGLIT (lb:lexbuf): string =
  match current_token() with
  | STRINGLIT s ->
      consume_token lb;
      s
  | _ ->
      expected "" [STRINGLIT""]

let consume_SWITCH (lb:lexbuf): bool =
  match current_token() with
  | SWITCH b ->
      consume_token lb;
      b
  | _ ->
      expected "" [SWITCH true]

let consume_INT (lb:lexbuf): string =
  match current_token() with
  | INT s ->
      consume_token lb;
      s
  | _ ->
      expected "" [INT""]

let qid (lb:lexbuf): (string list * string) loc =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
    match current_token() with
  | UID s ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 ([], s)
  | QID p ->
      let pos1 = current_pos() in
      consume_token lb;
      qid_of_path pos1 p
  | _ ->
      expected "" [UID"";QID[]]

let qid_expl (lb:lexbuf): (string list * string) loc =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
  | UID_EXPL s ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 ([], s)
  | QID_EXPL p ->
      let pos1 = current_pos() in
      consume_token lb;
      qid_of_path pos1 p
  | _ ->
      expected "" [UID_EXPL"";QID_EXPL[]]

let uid (lb:lexbuf): string loc =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
  | UID s ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 s
  | _ ->
      expected "" [UID""]

let param (lb:lexbuf): string loc option =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
  | UID s ->
      let pos1 = current_pos() in
      consume_token lb;
      Some (make_pos pos1 s)
  | UNDERSCORE ->
      consume_token lb;
      None
  | _ ->
      expected "non-qualified identifier or \"_\"" [UID"";UNDERSCORE]

let int (lb:lexbuf): string =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
  | INT s ->
      consume_token lb;
      s
  | _ ->
      expected "integer" [INT""]

let float_or_int (lb:lexbuf): string =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
  | INT s
  | FLOAT s ->
      consume_token lb;
      s
  | _ ->
      expected "integer or float" [INT"";FLOAT""]

let path (lb:lexbuf): string list loc =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
  (*| UID s ->
      let pos1 = current_pos() in
      LpLexer.syntax_error pos1 "Unqualified identifier"*)
  | QID p ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 (List.rev p)
  | _ ->
      expected "" [QID[]]

let qid_or_rule (lb:lexbuf): (string list * string) loc =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
  | UID s ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 ([], s)
  | QID p ->
      let pos1 = current_pos() in
      consume_token lb;
      qid_of_path pos1 p
  | UNIF_RULE ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 (Ghost.sign.sign_path, Unif_rule.equiv.sym_name)
  | COERCE_RULE ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 (Ghost.sign.sign_path, Coercion.coerce.sym_name)
  | _ ->
      expected "" [UID"";QID[];UNIF_RULE;COERCE_RULE]

let term_id (lb:lexbuf): p_term =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
  | UID _
  | QID _ ->
      let pos1 = current_pos() in
      let i = qid lb in
      make_pos pos1 (P_Iden(i, false))
  | UID_EXPL _
  | QID_EXPL _ ->
      let pos1 = current_pos() in
      let i = qid_expl lb in
      make_pos pos1 (P_Iden(i, true))
  | _ ->
      expected "" [UID"";QID[];UID_EXPL"";QID_EXPL[]]

(* commands *)

let rec command pos1 p_sym_mod (lb:lexbuf): p_command =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
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
      let pos1 = current_pos() in
      command pos1 (nelist modifier lb) lb
  (* qid *)
  | UID _
  | QID _ ->
      begin
        match p_sym_mod with
        | [{elt=P_opaq;_}] ->
            let i = qid lb in
            make_pos pos1 (P_opaque i)
        | [] ->
            expected "command keyword missing" []
        | {elt=P_opaq;_}::{pos;_}::_ ->
            expected "an opaque command must be followed by an identifier" []
        | _ ->
            expected "" [SYMBOL]
      end
  | REQUIRE ->
      if p_sym_mod <> [] then expected "" [SYMBOL]; (*or modifiers*)
      let pos1 = current_pos() in
      consume_token lb;
      begin
        match current_token() with
        | OPEN ->
            consume_token lb;
            let ps = nelist path lb in
            make_pos pos1 (P_require(true,ps))
        | _ ->
            let ps = nelist path lb in
            begin
              match current_token() with
              | AS ->
                  let p =
                    match ps with
                    | [p] -> p
                    | _ -> expected "a single module before \"as\"" []
                  in
                  consume_token lb;
                  let i = uid lb in
                  make_pos pos1 (P_require_as(p,i))
              | _ ->
                  make_pos pos1 (P_require(false,ps))
            end
      end
  | OPEN ->
      if p_sym_mod <> [] then expected "" [SYMBOL]; (*or modifiers*)
      let pos1 = current_pos() in
      consume_token lb;
      let l = list path lb in
      make_pos pos1 (P_open l)
  | SYMBOL ->
      let pos1 = current_pos() in
      consume_token lb;
      let p_sym_nam = uid lb in
      let p_sym_arg = list params lb in
      begin
        match current_token() with
        | COLON ->
            consume_token lb;
            let p_sym_typ = Some(term lb) in
            begin
              match current_token() with
              | BEGIN ->
                  let p_sym_prf = Some (proof lb) in
                  let p_sym_def = false in
                  let sym =
                    {p_sym_mod; p_sym_nam; p_sym_arg; p_sym_typ;
                     p_sym_trm=None; p_sym_def; p_sym_prf}
                  in make_pos pos1 (P_symbol(sym))
              | ASSIGN ->
                  consume_token lb;
                  let p_sym_trm, p_sym_prf = term_proof lb in
                  let p_sym_def = true in
                  let sym =
                    {p_sym_mod; p_sym_nam; p_sym_arg; p_sym_typ;
                     p_sym_trm; p_sym_def; p_sym_prf}
                  in make_pos pos1 (P_symbol(sym))
              | SEMICOLON ->
                  let p_sym_trm = None in
                  let p_sym_def = false in
                  let p_sym_prf = None in
                  let sym =
                    {p_sym_mod; p_sym_nam; p_sym_arg; p_sym_typ;
                     p_sym_trm; p_sym_def; p_sym_prf}
                  in make_pos pos1 (P_symbol(sym))
              | _ ->
                  expected "" [BEGIN;ASSIGN]
            end
        | ASSIGN ->
            consume_token lb;
            let p_sym_trm, p_sym_prf = term_proof lb in
            let p_sym_def = true in
            let p_sym_typ = None in
            let sym =
              {p_sym_mod; p_sym_nam; p_sym_arg; p_sym_typ;
               p_sym_trm; p_sym_def; p_sym_prf}
            in make_pos pos1 (P_symbol(sym))
        | _ ->
            expected "" [COLON;ASSIGN]
      end
  | L_PAREN
  | L_SQ_BRACKET ->
      let pos1 = current_pos() in
      let xs = nelist params lb in
      consume INDUCTIVE lb;
      let i = inductive lb in
      let is = list (prefix WITH inductive) lb in
      make_pos pos1 (P_inductive(p_sym_mod,xs,i::is))
  | INDUCTIVE ->
      let pos1 = current_pos() in
      consume_token lb;
      let i = inductive lb in
      let is = list (prefix WITH inductive) lb in
      make_pos pos1 (P_inductive(p_sym_mod,[],i::is))
  | RULE ->
      if p_sym_mod <> [] then expected "" [SYMBOL]; (*or modifiers*)
      let pos1 = current_pos() in
      consume_token lb;
      let r = rule lb in
      let rs = list (prefix WITH rule) lb in
      make_pos pos1 (P_rules(r::rs))
  | UNIF_RULE ->
      if p_sym_mod <> [] then expected "" [SYMBOL]; (*or modifiers*)
      let pos1 = current_pos() in
      consume_token lb;
      let e = equation lb in
      consume HOOK_ARROW lb;
      consume L_SQ_BRACKET lb;
      let eq1 = equation lb in
      let eqs = list (prefix SEMICOLON equation) lb in
      let es = eq1::eqs in
      consume R_SQ_BRACKET lb;
      (* FIXME: give sensible positions instead of Pos.none and P.appl. *)
      let equiv = P.qiden Ghost.sign.sign_path Unif_rule.equiv.sym_name in
      let cons = P.qiden Ghost.sign.sign_path Unif_rule.cons.sym_name in
      let mk_equiv (t, u) = P.appl (P.appl equiv t) u in
      let lhs = mk_equiv e in
      let es = List.rev_map mk_equiv es in
      let (en, es) = List.(hd es, tl es) in
      let cat e es = P.appl (P.appl cons e) es in
      let rhs = List.fold_right cat es en in
      let r = make_pos pos1 (lhs, rhs) in
      make_pos pos1 (P_unif_rule(r))
  | COERCE_RULE ->
      if p_sym_mod <> [] then expected "" [SYMBOL]; (*or modifiers*)
      let pos1 = current_pos() in
      consume_token lb;
      let r = rule lb in
      make_pos pos1 (P_coercion r)
  | BUILTIN ->
      if p_sym_mod <> [] then expected "" [SYMBOL]; (*or modifiers*)
      let pos1 = current_pos() in
      consume_token lb;
      begin
        match current_token() with
        | STRINGLIT s ->
            consume_token lb;
            consume ASSIGN lb;
            let i = qid lb in
            make_pos pos1 (P_builtin(s,i))
        | _ ->
            expected "" [STRINGLIT""]
      end
  | NOTATION ->
      if p_sym_mod <> [] then expected "" [SYMBOL]; (*or modifiers*)
      let pos1 = current_pos() in
      consume_token lb;
      let i = qid lb in
      let n = notation lb in
      make_pos pos1 (P_notation(i,n))
  | _ ->
      if p_sym_mod <> [] then expected "" [SYMBOL]; (*or modifiers*)
      let pos1 = current_pos() in
      let q = query lb in
      make_pos pos1 (P_query(q))

and inductive (lb:lexbuf): p_inductive =
  let pos0 = current_pos() in
  let i = uid lb in
  let pos1 = current_pos() in
  let ps = list params lb in
  consume COLON lb;
  let t = term lb in
  let pos2 = current_pos() in
  let t = make_prod (fst pos1) ps t (snd pos2) in
  consume ASSIGN lb;
  begin
    match current_token() with
    | UID _ ->
        let c = constructor lb in
        let cs = list (prefix VBAR constructor) lb in
        let l = c::cs in
        make_pos pos0 (i,t,l)
    | VBAR ->
        let l = list (prefix VBAR constructor) lb in
        make_pos pos0 (i,t,l)
    | SEMICOLON ->
        let l = [] in
        make_pos pos0 (i,t,l)
    | _ ->
        expected "identifier" []
    end

and constructor (lb:lexbuf): p_ident * p_term =
  let i = uid lb in
  let pos1 = current_pos() in
  let ps = list params lb in
  consume COLON lb;
  let t = term lb in
  i, make_prod (fst pos1) ps t (snd (current_pos()))

and modifier (lb:lexbuf): p_modifier =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
  | SIDE d ->
      let pos1 = current_pos() in
      consume_token lb;
      begin
        match current_token() with
        | ASSOCIATIVE ->
            consume_token lb;
            make_pos pos1 (P_prop (Term.Assoc((d = Pratter.Left))))
        | _ ->
            expected "" [ASSOCIATIVE]
      end
  | ASSOCIATIVE ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 (P_prop (Term.Assoc false))
  | COMMUTATIVE ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 (P_prop Term.Commu)
  | CONSTANT ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 (P_prop Term.Const)
  | INJECTIVE ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 (P_prop Term.Injec)
  | OPAQUE ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 P_opaq
  | SEQUENTIAL ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 (P_mstrat Term.Sequen)
  | _ ->
      exposition lb

and exposition (lb:lexbuf): p_modifier =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
  | PRIVATE ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 (P_expo Term.Privat)
  | PROTECTED ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 (P_expo Term.Protec)
  | _ ->
      expected "" [PRIVATE;PROTECTED]

and notation (lb:lexbuf): string Sign.notation =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
  | INFIX ->
      consume_token lb;
      begin
        match current_token() with
        | SIDE d ->
            consume_token lb;
            let p = float_or_int lb in
            Sign.Infix(d, p)
        | _ ->
            let p = float_or_int lb in
            Sign.Infix(Pratter.Neither, p)
      end
  | POSTFIX ->
      consume_token lb;
      let p = float_or_int lb in
      Sign.Postfix p
  | PREFIX ->
      consume_token lb;
      let p = float_or_int lb in
      Sign.Prefix p
  | QUANTIFIER ->
      consume_token lb;
      Sign.Quant
  | _ ->
      expected "" [INFIX;POSTFIX;PREFIX;QUANTIFIER]

and rule (lb:lexbuf): (p_term * p_term) loc =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  let pos1 = current_pos() in
  let l = term lb in
  consume HOOK_ARROW lb;
  let r = term lb in
  make_pos pos1 (l, r)

and equation (lb:lexbuf): p_term * p_term =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  let l = term lb in
  consume EQUIV lb;
  let r = term lb in
  (l, r)

(* queries *)

and query (lb:lexbuf): p_query =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
  | ASSERT b ->
      let pos1 = current_pos() in
      consume_token lb;
      let ps = list params lb in
      consume TURNSTILE lb;
      let t = term lb in
      begin
        match current_token() with
        | COLON ->
            consume_token lb;
            let a = term lb in
            let pos2 = current_pos() in
            let t = make_abst (fst pos1) ps t (snd pos2) in
            let a = make_prod (fst pos1) ps a (snd pos2) in
            make_pos pos1 (P_query_assert(b, P_assert_typing(t,a)))
        | EQUIV ->
            consume_token lb;
            let u = term lb in
            let pos2 = current_pos() in
            let t = make_abst (fst pos1) ps t (snd pos2) in
            let u = make_abst (fst pos1) ps u (snd pos2) in
            make_pos pos1 (P_query_assert(b, P_assert_conv(t, u)))
        | _ ->
            expected "" [COLON;EQUIV]
      end
  | COMPUTE ->
      let pos1 = current_pos() in
      consume_token lb;
      let t = term lb in
      make_pos pos1 (P_query_normalize(t, {strategy=SNF; steps=None}))
  | PRINT ->
      let pos1 = current_pos() in
      consume_token lb;
      begin
        match current_token() with
        | SEMICOLON ->
            make_pos pos1 (P_query_print None)
        | _ ->
            let i = qid_or_rule lb in
            make_pos pos1 (P_query_print (Some i))
      end
  | PROOFTERM ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 P_query_proofterm
  | DEBUG_FLAGS fl ->
      let pos1 = current_pos() in
      consume_token lb;
      let (b, s) = fl in
      make_pos pos1 (P_query_debug(b, s))
  | FLAG ->
      let pos1 = current_pos() in
      consume_token lb;
      let s = consume_STRINGLIT lb in
      let b = consume_SWITCH lb in
      make_pos pos1 (P_query_flag(s,b))
  | PROVER ->
      let pos1 = current_pos() in
      consume_token lb;
      let s = consume_STRINGLIT lb in
      make_pos pos1 (P_query_prover(s))
  | PROVER_TIMEOUT ->
      let pos1 = current_pos() in
      consume_token lb;
      let n = consume_INT lb in
      make_pos pos1 (P_query_prover_timeout n)
  | VERBOSE ->
      let pos1 = current_pos() in
      consume_token lb;
      let n = consume_INT lb in
      make_pos pos1 (P_query_verbose n)
  | TYPE_QUERY ->
      let pos1 = current_pos() in
      consume_token lb;
      let t = term lb in
      make_pos pos1 (P_query_infer(t, {strategy=NONE; steps=None}))
  | SEARCH ->
      let pos1 = current_pos() in
      consume_token lb;
      let q = search lb in
      make_pos pos1 (P_query_search q)
  | _ ->
      expected "query" []

and term_proof (lb:lexbuf): p_term option * (p_proof * p_proof_end) option =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
  | BEGIN ->
      let p = proof lb in
      None, Some p
  | _ ->
      let t = term lb in
      begin
        match current_token() with
        | BEGIN ->
            let p = proof lb in
            Some t, Some p
        | _ ->
            Some t, None
      end

(* proofs *)

and proof (lb:lexbuf): p_proof * p_proof_end =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  consume BEGIN lb;
  match current_token() with
  | L_CU_BRACKET ->
      let l = nelist subproof lb in
      if current_token() = SEMICOLON then consume_token lb;
      let pe = proof_end lb in
      l, pe
  (*queries*)
  | ASSERT _
  | COMPUTE
  | PRINT
  | PROOFTERM
  | DEBUG
  | FLAG
  | PROVER
  | PROVER_TIMEOUT
  | VERBOSE
  | SEARCH
  (*tactics*)
  | ADMIT
  | APPLY
  | ASSUME
  | FAIL
  | GENERALIZE
  | HAVE
  | INDUCTION
  | REFINE
  | REFLEXIVITY
  | REMOVE
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
      expected "subproof, tactic or query" []

and subproof (lb:lexbuf): p_proofstep list =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
  | L_CU_BRACKET ->
      consume_token lb;
      let l = steps lb in
      consume R_CU_BRACKET lb;
      l
  | _ ->
      expected "" [L_CU_BRACKET]

and steps (lb:lexbuf): p_proofstep list =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
  (*queries*)
  | ASSERT _
  | COMPUTE
  | PRINT
  | PROOFTERM
  | DEBUG
  | FLAG
  | PROVER
  | PROVER_TIMEOUT
  | VERBOSE
  | SEARCH
  (*tactics*)
  | ADMIT
  | APPLY
  | ASSUME
  | FAIL
  | GENERALIZE
  | HAVE
  | INDUCTION
  | REFINE
  | REFLEXIVITY
  | REMOVE
  | REWRITE
  | SET
  | SIMPLIFY
  | SOLVE
  | SYMMETRY
  | TRY
  | WHY3 ->
      let a = step lb in
      let acc = list (prefix SEMICOLON step) lb in
      if current_token() = SEMICOLON then consume_token lb;
      a::acc
  | END
  | ABORT
  | ADMITTED ->
      []
  | _ ->
      expected "tactic or query" []

and step (lb:lexbuf): p_proofstep =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  let t = tactic lb in
  let l = list subproof lb in
  Tactic(t, l)

and proof_end (lb:lexbuf): p_proof_end =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
  | ABORT ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 Syntax.P_proof_abort
  | ADMITTED ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 Syntax.P_proof_admitted
  | END ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 Syntax.P_proof_end
  | _ ->
      expected "" [ABORT;ADMITTED;END]

and tactic (lb:lexbuf): p_tactic =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
  (*queries*)
  | ASSERT _
  | COMPUTE
  | PRINT
  | PROOFTERM
  | DEBUG
  | FLAG
  | PROVER
  | PROVER_TIMEOUT
  | VERBOSE
  | SEARCH ->
      let pos1 = current_pos() in
      make_pos pos1 (P_tac_query (query lb))
  | ADMIT ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 P_tac_admit
  | APPLY ->
      let pos1 = current_pos() in
      consume_token lb;
      let t = term lb in
      make_pos pos1 (P_tac_apply t)
  | ASSUME ->
      let pos1 = current_pos() in
      consume_token lb;
      let xs = nelist param lb in
      make_pos pos1 (P_tac_assume xs)
  | FAIL ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 P_tac_fail
  | GENERALIZE ->
      let pos1 = current_pos() in
      consume_token lb;
      let i = uid lb in
      make_pos pos1 (P_tac_generalize i)
  | HAVE ->
      let pos1 = current_pos() in
      consume_token lb;
      let i = uid lb in
      consume COLON lb;
      let t = term lb in
      make_pos pos1 (P_tac_have(i,t))
  | INDUCTION ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 P_tac_induction
  | REFINE ->
      let pos1 = current_pos() in
      consume_token lb;
      let t = term lb in
      make_pos pos1 (P_tac_refine t)
  | REFLEXIVITY ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 P_tac_refl
  | REMOVE ->
      let pos1 = current_pos() in
      consume_token lb;
      let xs = nelist uid lb in
      make_pos pos1 (P_tac_remove xs)
  | REWRITE ->
      let pos1 = current_pos() in
      consume_token lb;
      begin
        match current_token() with
        | SIDE d ->
            consume_token lb;
            begin
              match current_token() with
              | DOT ->
                  consume_token lb;
                  let p = rw_patt_spec lb in
                  let t = term lb in
                  let b = d <> Pratter.Left in
                  make_pos pos1 (P_tac_rewrite(b,Some p,t))
              | _ ->
                  let t = term lb in
                  let b = d <> Pratter.Left in
                  make_pos pos1 (P_tac_rewrite(b,None,t))
            end
        | DOT ->
            consume_token lb;
            let p = rw_patt_spec lb in
            let t = term lb in
            make_pos pos1 (P_tac_rewrite(true,Some p,t))
        | _ ->
            let t = term lb in
            make_pos pos1 (P_tac_rewrite(true,None,t))
      end
  | SET ->
      let pos1 = current_pos() in
      consume_token lb;
      let i = uid lb in
      consume ASSIGN lb;
      let t = term lb in
      make_pos pos1 (P_tac_set(i,t))
  | SIMPLIFY ->
      let pos1 = current_pos() in
      consume_token lb;
      begin
        match current_token() with
        | UID _
        | QID _ ->
            let i = Some (qid lb) in
            make_pos pos1 (P_tac_simpl i)
        | _ ->
            let i = None in
            make_pos pos1 (P_tac_simpl i)
      end
  | SOLVE ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 P_tac_solve
  | SYMMETRY ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 P_tac_sym
  | TRY ->
      let pos1 = current_pos() in
      consume_token lb;
      let t = tactic lb in
      make_pos pos1 (P_tac_try t)
  | WHY3 ->
      let pos1 = current_pos() in
      consume_token lb;
      begin
        match current_token() with
        | STRINGLIT s ->
            make_pos pos1 (P_tac_why3 (Some s))
        | _ ->
            make_pos pos1 (P_tac_why3 None)
      end
  | _ ->
      expected "tactic" []

and rw_patt (lb:lexbuf): p_rw_patt =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
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
  | INT _ ->
      let pos1 = current_pos() in
      let t1 = term lb in
      begin
        match current_token() with
        | IN ->
            consume_token lb;
            let t2 = term lb in
            begin
              match current_token() with
              | IN ->
                  consume_token lb;
                  let t3 = term lb in
                  let x = ident_of_term pos1 t2 in
                  make_pos pos1 (Rw_TermInIdInTerm(t1,(x,t3)))
              | _ ->
                  let x = ident_of_term pos1 t1 in
                  make_pos pos1 (Rw_IdInTerm(x,t2))
            end
        | AS ->
            consume_token lb;
            let t2 = term lb in
            begin
              match current_token() with
              | IN ->
                  consume_token lb;
                  let t3 = term lb in
                  let x = ident_of_term pos1 t2 in
                  make_pos pos1 (Rw_TermAsIdInTerm(t1,(x,t3)))
              | _ ->
                  expected "" [IN]
            end
        | _ ->
            make_pos pos1 (Rw_Term(t1))
      end
  | IN ->
      let pos1 = current_pos() in
      consume_token lb;
      let t1 = term lb in
      begin
        match current_token() with
        | IN ->
            consume_token lb;
            let t2 = term lb in
            let x = ident_of_term pos1 t1 in
            make_pos pos1 (Rw_InIdInTerm(x,t2))
        | _ ->
            make_pos pos1 (Rw_InTerm(t1))
      end
  | _ ->
      expected "term or keyword \"in\"" []

and rw_patt_spec (lb:lexbuf): p_rw_patt =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
  | L_SQ_BRACKET ->
      consume_token lb;
      let p = rw_patt lb in
      consume R_SQ_BRACKET lb; (*add info on opening bracket*)
      p
  | _ ->
      expected "" [L_SQ_BRACKET]

(* terms *)

and params (lb:lexbuf): p_params =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
  | L_PAREN ->
      consume_token lb;
      let ps = nelist param lb in
      begin
        match current_token() with
        | COLON ->
            consume_token lb;
            let typ = term lb in
            consume R_PAREN lb;
            ps, Some typ, false
        | R_PAREN ->
            consume_token lb;
            ps, None, false
        | _ ->
            expected "" [COLON;R_PAREN]
      end
  | L_SQ_BRACKET ->
      consume_token lb;
      let ps = nelist param lb in
      begin
        match current_token() with
        | COLON ->
            consume_token lb;
            let typ = term lb in
            consume R_SQ_BRACKET lb;
            ps, Some typ, true
        | R_SQ_BRACKET ->
            consume_token lb;
            ps, None, true
        | _ ->
            expected "" [COLON;R_SQ_BRACKET]
      end
  | _ ->
      let x = param lb in
      [x], None, false

and term (lb:lexbuf): p_term =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
  (* bterm *)
  | BACKQUOTE
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
  | INT _ ->
      let pos1 = current_pos() in
      let h = aterm lb in
      app pos1 h lb
  | _ ->
      expected "term" []

and app (pos1:position * position) (t: p_term) (lb:lexbuf): p_term =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
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
  | INT _ ->
      let u = aterm lb in
      app pos1 (make_pos pos1 (P_Appl(t,u))) lb
  (* bterm *)
  | BACKQUOTE
  | PI
  | LAMBDA
  | LET ->
      let u = bterm lb in
      make_pos pos1 (P_Appl(t,u))
  (* other cases *)
  | ARROW ->
      consume_token lb;
      let u = term lb in
      make_pos pos1 (P_Arro(t,u))
  | _ ->
      t

and bterm (lb:lexbuf): p_term =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
  | BACKQUOTE ->
      let pos1 = current_pos() in
      consume_token lb;
      let q = term_id lb in
      let b = binder lb in
      let b = make_pos pos1 (P_Abst(fst b, snd b)) in
      make_pos pos1 (P_Appl(q, b))
  | PI ->
      let pos1 = current_pos() in
      consume_token lb;
      let b = binder lb in
      make_pos pos1 (P_Prod(fst b, snd b))
  | LAMBDA ->
      let pos1 = current_pos() in
      consume_token lb;
      let b = binder lb in
      make_pos pos1 (P_Abst(fst b, snd b))
  | LET ->
      let pos1 = current_pos() in
      consume_token lb;
      let x = uid lb in
      let a = list params lb in
      begin
        match current_token() with
        | COLON ->
            consume_token lb;
            let b = Some (term lb) in
            consume ASSIGN lb;
            let t = term lb in
            consume IN lb;
            let u = term lb in
            make_pos pos1 (P_LLet(x, a, b, t, u))
        | _ ->
            let b = None in
            consume ASSIGN lb;
            let t = term lb in
            consume IN lb;
            let u = term lb in
            make_pos pos1 (P_LLet(x, a, b, t, u))
      end
  | _ ->
      expected "" [BACKQUOTE;PI;LAMBDA;LET]

and aterm (lb:lexbuf): p_term =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
    | UID _
    | QID _
    | UID_EXPL _
    | QID_EXPL _ ->
        term_id lb
    | UNDERSCORE ->
        let pos1 = current_pos() in
        consume_token lb;
        make_pos pos1 P_Wild
    | TYPE_TERM ->
        let pos1 = current_pos() in
        consume_token lb;
        make_pos pos1 P_Type
    | UID_META s ->
        let pos1 = current_pos() in
        consume_token lb;
        let i = make_pos pos1 s in
        begin
          match current_token() with
          | DOT ->
              consume_token lb;
              make_pos pos1 (P_Meta(i,Array.of_list (env lb)))
          | _ ->
              make_pos pos1 (P_Meta(i,[||]))
        end
    | UID_PATT s ->
        let pos1 = current_pos() in
        consume_token lb;
        let i = if s = "_" then None else Some(make_pos pos1 s) in
        begin
          match current_token() with
          | DOT ->
              consume_token lb;
              make_pos pos1 (P_Patt(i, Some(Array.of_list (env lb))))
          | _ ->
              make_pos pos1 (P_Patt(i, None))
        end
    | L_PAREN ->
        let pos1 = current_pos() in
        consume_token lb;
        let t = term lb in
        consume R_PAREN lb;
        make_pos pos1 (P_Wrap(t))
    | L_SQ_BRACKET ->
        let pos1 = current_pos() in
        consume_token lb;
        let t = term lb in
        consume R_SQ_BRACKET lb;
        make_pos pos1 (P_Expl(t))
    | INT n ->
        let pos1 = current_pos() in
        consume_token lb;
        make_pos pos1 (P_NLit n)
    | _ ->
        expected "identifier, \"_\", or term between parentheses or square \
                  brackets" []

and env (lb:lexbuf): p_term list =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
  | L_SQ_BRACKET ->
      consume_token lb;
      begin
        match current_token() with
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
      expected "" [L_SQ_BRACKET]

and binder (lb:lexbuf): p_params list * p_term =
  (*if log_enabled() then log "Expected: %s" __FUNCTION__;*)
  match current_token() with
  | UID _
  | UNDERSCORE ->
      let s = param lb in
      begin
        match current_token() with
        | UID _
        | UNDERSCORE
        | L_PAREN
        | L_SQ_BRACKET ->
            let ps = list params lb in
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
      end
  | L_PAREN ->
      let ps = nelist params lb in
      begin
        match current_token() with
        | COMMA ->
            consume_token lb;
            ps, term lb
        | _ ->
            expected "" [COMMA]
      end
  | L_SQ_BRACKET ->
      let ps = nelist params lb in
      begin
        match current_token() with
        | COMMA ->
            consume_token lb;
            ps, term lb
        | _ ->
            expected "" [COMMA]
      end
  | _ ->
      expected "" [UID"";UNDERSCORE;L_PAREN;L_SQ_BRACKET]

(* search *)

and where (lb:lexbuf): bool * inside option =
  if log_enabled() then log "Expected: %s" __FUNCTION__;
  match current_token() with
  | UID u ->
      let r =
        match u with
        | "=" -> Some Exact
        | ">" -> Some Inside
        | "≥"
        | ">=" -> None
        | _ -> expected "\">\", \"=\", \"≥\",\">=\"" []
      in
      consume_token lb;
      let g =
        match current_token() with
        | GENERALIZE -> consume_token lb; true
        | _ -> false
      in
      g,r
  | _ ->
      expected "\">\", \"=\", \"≥\",\">=\"" []

and asearch (lb:lexbuf): query =
  if log_enabled() then log "Expected: %s" __FUNCTION__;
  match current_token() with
  | TYPE_QUERY ->
      consume_token lb;
      let g, w = where lb in
      let t = aterm lb in
      if w <> None then expected "\"≥\", \">=\"" []
      else QBase(QSearch(t,g,Some(QType None)))
  | RULE ->
      consume_token lb;
      let g, w = where lb in
      let t = aterm lb in
      QBase(QSearch(t,g,Some(QXhs(w,None))))
  | UID k ->
      consume_token lb;
      let g, w = where lb in
      let t = aterm lb in
      begin
        match k, t.elt with
        | "name", P_Iden(id,false) ->
            assert (fst id.elt = []);
            if w <> Some Exact then expected "\"=\"" []
            else if g then
              expected "\"generalize\" cannot be used with \"name\"" []
            else QBase(QName(snd id.elt))
        | "name", _ ->
            expected "path prefix" []
        | "anywhere", _ ->
            if w <> None then expected "\"≥\", \">=\"" []
            else QBase(QSearch(t,g,None))
        | "spine",_ ->
            QBase(QSearch(t,g,Some(QType(Some(Spine w)))))
        | "concl",_ ->
            QBase(QSearch(t,g,Some(QType(Some(Conclusion w)))))
        | "hyp",_ ->
            QBase(QSearch(t,g,Some(QType(Some(Hypothesis w)))))
        | "lhs",_ ->
            QBase(QSearch(t,g,Some(QXhs(w,Some Lhs))))
        | "rhs",_ ->
            QBase(QSearch(t,g,Some(QXhs(w,Some Rhs))))
        | _ ->
            expected "Unknown keyword" []
      end
  | L_PAREN ->
      consume_token lb;
      let q = search lb in
      consume R_PAREN lb;
      q
  | _ ->
      expected "name, anywhere, rule, lhs, rhs, type, concl, hyp, spine" []

and csearch (lb:lexbuf): query =
  if log_enabled() then log "Expected: %s" __FUNCTION__;
  let aq = asearch lb in
  match current_token() with
  | COMMA ->
      let aqs = list (prefix COMMA asearch) lb in
      List.fold_left (fun x aq -> QOpp(x,Intersect,aq)) aq aqs
  | _ ->
      aq

and ssearch (lb:lexbuf): query =
  if log_enabled() then log "Expected: %s" __FUNCTION__;
  let cq = csearch lb in
  match current_token() with
  | SEMICOLON ->
      let cqs = list (prefix SEMICOLON csearch) lb in
      List.fold_left (fun x cq -> QOpp(x,Union,cq)) cq cqs
  | _ ->
      cq

and search (lb:lexbuf): query =
  if log_enabled() then log "Expected: %s" __FUNCTION__;
  let q = ssearch lb in
  let qids = list (prefix VBAR qid) lb in
  let path_of_qid qid =
    let p,n = qid.elt in
    if p = [] then n
    else Format.asprintf "%a.%a" Print.path p Print.uid n
  in
  List.fold_left (fun x qid -> QFilter(x,Path(path_of_qid qid))) q qids

let command (lb:lexbuf): p_command =
  if log_enabled() then log "------------------- start reading command";
  consume_token lb;
  if current_token() = EOF then raise End_of_file
  else
    let c = command (dummy_pos,dummy_pos) [] lb in
    match current_token() with
    | SEMICOLON -> c
    | _ -> expected "" [SEMICOLON]
