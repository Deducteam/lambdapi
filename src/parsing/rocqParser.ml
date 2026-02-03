open Lplib
open Common open Pos open Logger
open Syntax
open Core
open RocqLexer
open Lexing
open Sedlexing

let log = LpParser.log

(* token management *)

let string_of_token = function
  | EOF -> "end of file"
  | ARROW -> "→"
  | ASSIGN -> "≔"
  | BACKQUOTE -> "`"
  | COLON -> ":"
  | COMMA -> ","
  | DOT -> "."
  | GENERALIZE -> "generalize"
  | EXISTS -> "exists"
  | FORALL -> "forall"
  | FUN -> "fun"
  | THICKARROW -> "=>"
  | IN -> "in"
  | INT _ -> "integer"
  | LAMBDA -> "λ"
  | LET -> "let"
  | L_PAREN -> "("
  | L_SQ_BRACKET -> "["
  | PI -> "Π"
  | QID _ -> "qualified identifier"
  | QID_EXPL _ -> "@-prefixed qualified identifier"
  | RULE -> "rule"
  | R_PAREN -> ")"
  | R_SQ_BRACKET -> "]"
  | SEMICOLON -> ";"
  | STRINGLIT _ -> "string literal"
  | TYPE_QUERY -> "type"
  | TYPE_TERM -> "TYPE"
  | UID _ -> "non-qualified identifier"
  | UID_EXPL _ -> "@-prefixed non-qualified identifier"
  | UID_META _ -> "?-prefixed metavariable number"
  | UID_PATT _ -> "$-prefixed non-qualified identifier"
  | UNDERSCORE -> "_"
  | VBAR -> "|"

let pp_token ppf t = Base.string ppf (string_of_token t)

let the_current_token : (token * position * position) Stdlib.ref =
  Stdlib.ref dummy_token

let current_token() : token = let (t,_,_) = !the_current_token in t

let current_pos() : position * position =
  let (_,p1,p2) = !the_current_token in (p1,p2)
(*
let new_parsing (entry:lexbuf -> 'a) (lb:lexbuf): 'a =
  let t = !the_current_token in
  let reset() = the_current_token := t in
  the_current_token := LpLexer.token lb;
  try let r = entry lb in begin reset(); r end
  with e -> begin reset(); raise e end
 *)
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
  the_current_token := RocqLexer.token lb;
  if log_enabled() then
    let (t,p1,p2) = !the_current_token in
    let p = locate (p1,p2) in
    log "read new token %a %a" Pos.short (Some p) pp_token t

(* building positions and terms *)

let extend_pos (*s:string*) (lps:position * position): 'a -> 'a loc =
  let p1 = fst lps and p2 = fst (current_pos()) in
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

let make_abst (pos1:position) (ps:p_params list) (t:p_term) (pos2:position)
    :p_term =
  if ps = [] then t
  else extend_pos (*__FUNCTION__*) (pos1,pos2) (P_Abst(ps,t))

let make_prod (pos1:position) (ps:p_params list) (t:p_term) (pos2:position)
    :p_term =
  if ps = [] then t
  else extend_pos (*__FUNCTION__*) (pos1,pos2) (P_Prod(ps,t))

let ident_of_term pos1 {elt; _} =
  match elt with
  | P_Iden({elt=([], x); pos}, _) -> Pos.make pos x
  | _ -> LpLexer.syntax_error pos1 "not an unqualified identifier."

(* generic parsing functions *)

let list (elt:lexbuf -> 'a) (lb:lexbuf): 'a list =
  if log_enabled() then log "%s" __FUNCTION__;
  let acc = ref [] in
  (try while true do acc := elt lb :: !acc done with SyntaxError _ -> ());
  List.rev !acc

let nelist (elt:lexbuf -> 'a) (lb:lexbuf): 'a list =
  if log_enabled() then log "%s" __FUNCTION__;
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


let consume_INT (lb:lexbuf): string =
  match current_token() with
  | INT s ->
      consume_token lb;
      s
  | _ ->
      expected "" [INT""]


let qid (lb:lexbuf): (string list * string) loc =
  if log_enabled() then log "%s" __FUNCTION__;
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
  if log_enabled() then log "%s" __FUNCTION__;
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
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token() with
  | UID s ->
      let pos1 = current_pos() in
      consume_token lb;
      make_pos pos1 s
  | _ ->
      expected "" [UID""]

let param (lb:lexbuf): string loc option =
  if log_enabled() then log "%s" __FUNCTION__;
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
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token() with
  | INT s ->
      consume_token lb;
      s
  | _ ->
      expected "integer" [INT""]

let path (lb:lexbuf): string list loc =
  if log_enabled() then log "%s" __FUNCTION__;
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

let rec term_id (lb:lexbuf): p_term =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token() with
  | UID _
  | QID _ ->
      let i = qid lb in
      {i with elt=P_Iden(i, false)}
  | UID_EXPL _
  | QID_EXPL _ ->
      let i = qid_expl lb in
      {i with elt=P_Iden(i, true)}
  | _ ->
      expected "" [UID"";QID[];UID_EXPL"";QID_EXPL[]]

(* commands *)

and rwpatt_content (lb:lexbuf): p_rwpatt =
  if log_enabled() then log "%s" __FUNCTION__;
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
  | INT _
  (* | QINT _ *)
  | STRINGLIT _ ->
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
                  extend_pos (*__FUNCTION__*) pos1
                    (Rw_TermInIdInTerm(t1,(x,t3)))
              | _ ->
                  let x = ident_of_term pos1 t1 in
                  extend_pos (*__FUNCTION__*) pos1 (Rw_IdInTerm(x,t2))
            end
        | _ ->
            extend_pos (*__FUNCTION__*) pos1 (Rw_Term(t1))
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
            extend_pos (*__FUNCTION__*) pos1 (Rw_InIdInTerm(x,t2))
        | _ ->
            extend_pos (*__FUNCTION__*) pos1 (Rw_InTerm(t1))
      end
  | _ ->
      expected "term or keyword \"in\"" []

and rwpatt_bracket (lb:lexbuf): p_rwpatt =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token() with
  | L_SQ_BRACKET ->
      consume_token lb;
      let p = rwpatt_content lb in
      consume R_SQ_BRACKET lb; (*add info on opening bracket*)
      p
  | _ ->
      expected "" [L_SQ_BRACKET]

and rwpatt (lb:lexbuf): p_rwpatt =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token() with
  | DOT ->
      consume_token lb;
      rwpatt_bracket lb
  | _ ->
      expected "" [DOT]

(* terms *)

and params (lb:lexbuf): p_params =
  if log_enabled() then log "%s" __FUNCTION__;
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

and fun_param_list (lb:lexbuf) =
  if log_enabled() then log "%s" __FUNCTION__;
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
  | _ ->
      let x = param lb in
      [x], None, false

and term (lb:lexbuf): p_term =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token() with
  (* bterm *)
  | BACKQUOTE
  | EXISTS
  | FORALL
  | FUN
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
  | STRINGLIT _ ->
      let pos1 = current_pos() in
      let h = aterm lb in
      app pos1 h lb
  | _ ->
      expected "term" []

and app (pos1:position * position) (t: p_term) (lb:lexbuf): p_term =
  if log_enabled() then log "%s" __FUNCTION__;
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
  | INT _
  | STRINGLIT _ ->
      let u = aterm lb in
      app pos1 (extend_pos (*__FUNCTION__*) pos1 (P_Appl(t,u))) lb
  (* bterm *)
  | BACKQUOTE
  | PI
  | LAMBDA
  | LET ->
      let u = bterm lb in
      extend_pos (*__FUNCTION__*) pos1 (P_Appl(t,u))
  (* other cases *)
  | ARROW ->
      consume_token lb;
      let u = term lb in
      extend_pos (*__FUNCTION__*) pos1 (P_Arro(t,u))
  | _ ->
      t

and bterm (lb:lexbuf): p_term =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token() with
  | BACKQUOTE ->
      let pos1 = current_pos() in
      consume_token lb;
      let q = term_id lb in
      let b = binder lb in
      let b = extend_pos (*__FUNCTION__*) pos1 (P_Abst(fst b, snd b)) in
      extend_pos (*__FUNCTION__*) pos1 (P_Appl(q, b))
  | EXISTS ->
      let pos1 = current_pos() in
      consume_token lb;
      let b = rocqbinder lb COMMA in
          let f = fun bin res ->
            extend_pos pos1 (P_Appl(
              extend_pos pos1 (P_Iden(extend_pos pos1 ([],"∃"), false)),
              extend_pos pos1 (P_Abst([bin], res)))) in
       (List.fold_right f (fst b) (snd b))
  | FORALL ->
    (* { make_pos $sloc (P_Prod(fst b, snd b)) }  *)
      let pos1 = current_pos() in
      consume_token lb;
      let b = rocqbinder lb COMMA in
      extend_pos (*__FUNCTION__*) pos1 (P_Prod(fst b, snd b))
  | PI ->
    (* { make_pos $sloc (P_Prod(fst b, snd b)) }  *)
      let pos1 = current_pos() in
      consume_token lb;
      let b = binder lb in
      extend_pos (*__FUNCTION__*) pos1 (P_Prod(fst b, snd b))
  | LAMBDA ->
      let pos1 = current_pos() in
      consume_token lb;
      let b = binder lb in
      extend_pos (*__FUNCTION__*) pos1 (P_Abst(fst b, snd b))
  | FUN ->
      let pos1 = current_pos() in
      consume_token lb;
      let b = rocqbinder lb THICKARROW in
      extend_pos (*__FUNCTION__*) pos1 (P_Abst(fst b, snd b))
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
            extend_pos (*__FUNCTION__*) pos1 (P_LLet(x, a, b, t, u))
        | _ ->
            let b = None in
            consume ASSIGN lb;
            let t = term lb in
            consume IN lb;
            let u = term lb in
            extend_pos (*__FUNCTION__*) pos1 (P_LLet(x, a, b, t, u))
      end
  | _ ->
      expected "" [BACKQUOTE;PI;LAMBDA;LET]

and aterm (lb:lexbuf): p_term =
  if log_enabled() then log "%s" __FUNCTION__;
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
              extend_pos (*__FUNCTION__*) pos1
                (P_Meta(i,Array.of_list (env lb)))
          | _ ->
              {i with elt=P_Meta(i,[||])}
        end
    | UID_PATT s ->
        let pos1 = current_pos() in
        consume_token lb;
        let i =
          if s = "_" then None else Some(make_pos pos1 s) in
        begin
          match current_token() with
          | DOT ->
              consume_token lb;
              extend_pos (*__FUNCTION__*) pos1
                (P_Patt(i, Some(Array.of_list (env lb))))
          | _ ->
              make_pos pos1 (P_Patt(i, None))
        end
    | L_PAREN ->
        let pos1 = current_pos() in
        consume_token lb;
        let t = term lb in
        consume R_PAREN lb;
        extend_pos (*__FUNCTION__*) pos1 (P_Wrap(t))
    | L_SQ_BRACKET ->
        let pos1 = current_pos() in
        consume_token lb;
        let t = term lb in
        consume R_SQ_BRACKET lb;
        extend_pos (*__FUNCTION__*) pos1 (P_Expl(t))
    | INT n ->
        let pos1 = current_pos() in
        consume_token lb;
        make_pos pos1 (P_NLit([],n))
    | STRINGLIT s ->
        let pos1 = current_pos() in
        consume_token lb;
        make_pos pos1 (P_SLit s)
    | _ ->
        expected "identifier, \"_\", or term between parentheses or square \
                  brackets" []

and env (lb:lexbuf): p_term list =
  if log_enabled() then log "%s" __FUNCTION__;
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
  if log_enabled() then log "%s" __FUNCTION__;
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

and rocqbinder (lb:lexbuf) terminator : p_params list * p_term =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token() with
  | UID _
  | UNDERSCORE ->
      let s = param lb in
      begin
        match current_token() with
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
            if current_token() = terminator then
                begin
                    consume_token lb;
                    let p = [s], None, false in
                    [p], term lb
                end
            else
            expected "parameter list"
              [UID"";UNDERSCORE;L_PAREN;terminator]
      end
  | L_PAREN ->
      let ps = nelist params lb in
      begin
        match current_token() with
        | _ ->
            if current_token() = terminator then
                begin
                    consume_token lb;
                    ps, term lb
                end
            else
            expected "" [terminator]
      end
  | _ ->
      expected "" [UID"";UNDERSCORE;L_PAREN;]


(* search *)

and generalize (lb:lexbuf): bool =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token() with
  | GENERALIZE -> consume_token lb; true
  | _ -> false

and relation (lb:lexbuf): relation option =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token() with
  | UID "=" -> consume_token lb; Some Exact
  | UID ">" -> consume_token lb; Some Inside
  | UID ("≥"|">=") -> consume_token lb; None
  | _ -> expected "\">\", \"=\", \"≥\",\">=\"" []

and where (lb:lexbuf): bool * relation option =
  if log_enabled() then log "%s" __FUNCTION__;
  let r = relation lb in
  let g = generalize lb in
  g,r

and asearch (lb:lexbuf): search =
  if log_enabled() then log "%s" __FUNCTION__;
  match current_token() with
  | UID "name" ->
      begin
        consume_token lb;
        match current_token() with
        | UID "=" ->
            consume_token lb;
            QBase(QName (uid lb).elt)
        | _ -> expected "\"=\"" []
      end
  | TYPE_QUERY ->
      begin
        consume_token lb;
        match current_token() with
        | UID ("≥"|">=") ->
            consume_token lb;
            let g = generalize lb in
            let t = term lb in
            QBase(QSearch(t,g,Some(QType None)))
        | _ -> expected "\"≥\",\">=\"" []
      end
  | UID "anywhere" ->
      begin
        consume_token lb;
        match current_token() with
        | UID ("≥"|">=") ->
            consume_token lb;
            let g = generalize lb in
            let t = term lb in
            QBase(QSearch(t,g,None))
        | _ -> expected "\"≥\",\">=\"" []
      end
  | RULE ->
      consume_token lb;
      let r = relation lb in
      let g = generalize lb in
      let t = term lb in
      QBase(QSearch(t,g,Some(QXhs(r,None))))
  | UID "spine" ->
    begin
        consume_token lb;
      let r = relation lb in
      let g = generalize lb in
      let t = term lb in
      QBase(QSearch(t,g,Some(QType(Some(Spine r)))))
    end
  | UID "concl" ->
    begin
        consume_token lb;
      let r = relation lb in
      let g = generalize lb in
      let t = term lb in
      QBase(QSearch(t,g,Some(QType(Some(Conclusion r)))))
    end
  | UID "hyp" ->
    begin
        consume_token lb;
      let r = relation lb in
      let g = generalize lb in
      let t = term lb in
      QBase(QSearch(t,g,Some(QType(Some(Hypothesis r)))))
    end
  | UID "lhs" ->
    begin
        consume_token lb;
      let r = relation lb in
      let g = generalize lb in
      let t = term lb in
      QBase(QSearch(t,g,Some(QXhs(r,Some Lhs))))
    end
  | UID "rhs" ->
    begin
        consume_token lb;
      let r = relation lb in
      let g = generalize lb in
      let t = term lb in
      QBase(QSearch(t,g,Some(QXhs(r,Some Rhs))))
    end
  | L_PAREN ->
      consume_token lb;
      let q = search lb in
      consume R_PAREN lb;
      q
  | _ ->
      expected "name, anywhere, rule, lhs, rhs, type, concl, hyp, spine" []

and csearch (lb:lexbuf): search =
  if log_enabled() then log "%s" __FUNCTION__;
  let aq = asearch lb in
  match current_token() with
  | COMMA ->
      let aqs = list (prefix COMMA asearch) lb in
      List.fold_left (fun x aq -> QOp(x,Intersect,aq)) aq aqs
  | _ ->
      aq

and ssearch (lb:lexbuf): search =
  if log_enabled() then log "%s" __FUNCTION__;
  let cq = csearch lb in
  match current_token() with
  | SEMICOLON ->
      let cqs = list (prefix SEMICOLON csearch) lb in
      List.fold_left (fun x cq -> QOp(x,Union,cq)) cq cqs
  | _ ->
      cq

and search (lb:lexbuf): search =
  (*  expected "prbolem " []*)
   if log_enabled() then log "%s" __FUNCTION__;
  let q = ssearch lb in
  let qids = list (prefix VBAR qid) lb in
  let path_of_qid qid =
    let p,n = qid.elt in
    if p = [] then n
    else Format.asprintf "%a.%a" Print.path p Print.uid n
  in
  List.fold_left (fun x qid -> QFilter(x,Path(path_of_qid qid))) q qids
