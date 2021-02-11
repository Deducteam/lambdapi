(** Pretty-printing the parser-level AST.

    This module defines functions that allow printing elements of syntax found
    in the parser-level abstract syntax. This is used, for example, to print a
    file in the Lambdapi syntax, given the AST obtained when parsing a file in
    the legacy (Dedukti) syntax. *)

open! Lplib
open Base
open Common
open Console
open Pos
open Syntax
open Format

let ident : p_ident pp = fun ppf {pos; elt=s} ->
  if LpLexer.is_keyword s then
    fatal pos "Identifier [%s] is a Lambdapi keyword." s
  else pp_print_string ppf s

let arg_ident : p_ident option pp = fun ppf idopt ->
  match idopt with
  | Some(id) -> ident ppf id
  | None     -> pp_print_string ppf "_"

let p_mod : p_mod pp = fun ppf {elt=mp;_} -> Path.pp ppf mp

let qident : p_qident pp = fun ppf {elt=(mp,s); pos} ->
  if LpLexer.is_keyword s then
    fatal pos "Identifier [%s] is a Lambdapi keyword." s
  else match mp with
       | [] -> pp_print_string ppf s
       | _::_ -> fprintf ppf "%a.%s" Path.pp mp s

let modifier : p_modifier pp = fun ppf {elt; _} ->
  match elt with
  | P_expo(e)   -> Tags.pp_expo ppf e
  | P_mstrat(s) -> Tags.pp_match_strat ppf s
  | P_prop(p)   -> Tags.pp_prop ppf p
  | P_opaq      -> Format.pp_print_string ppf "opaque "

let rec term : p_term pp = fun ppf t ->
  let out fmt = fprintf ppf fmt in
  let empty_context = ref true in
  let rec pp p _ t =
    let env _ ar =
      match ar with
      | None -> ()
      | Some [||] when !empty_context -> ()
      | Some ar -> out "[%a]" (Array.pp func "; ") ar
    in
    match (t.elt, p) with
    | (P_Type              , _    ) -> out "TYPE"
    | (P_Iden(qid,_)       , _    ) -> out "%a" qident qid
    | (P_Wild              , _    ) -> out "_"
    | (P_Meta(x,ar)        , _    ) -> out "?%a%a" ident x env ar
    | (P_Patt(None   ,ar)  , _    ) -> out "$_%a" env ar
    | (P_Patt(Some(x),ar)  , _    ) -> out "$%a%a" ident x env ar
    | (P_Appl(t,u)         , `PAppl)
    | (P_Appl(t,u)         , `PFunc) -> out "%a %a" appl t atom u
    | (P_Impl(a,b)         , `PFunc) -> out "%a → %a" appl a func b
    | (P_Abst(xs,t)        , `PFunc) ->
        out "λ%a, " args_list xs;
        let fn (ids,_,_) = List.for_all ((=) None) ids in
        let ec = !empty_context in
        empty_context := ec && List.for_all fn xs;
        out "%a" func t;
        empty_context := ec
    | (P_Prod(xs,b)        , `PFunc) ->
        out "Π%a, %a" args_list xs func b
    | (P_LLet(x,xs,a,t,u)  , `PFunc) ->
        out "@[<hov 2>let %a%a%a ≔@ %a@] in %a"
          ident x args_list xs annot a func t func u
    | (P_NLit(i)           , _    ) -> out "%i" i
    (* We print minimal parentheses, and ignore the [Wrap] constructor. *)
    | (P_Wrap(t)           , _    ) -> out "%a" (pp p) t
    | (P_Expl(t)           , _    ) -> out "{%a}" func t
    | (_                   , _    ) -> out "(%a)" func t
  and atom ppf t = pp `PAtom ppf t
  and appl ppf t = pp `PAppl ppf t
  and func ppf t = pp `PFunc ppf t
  in
  let rec toplevel _ t =
    match t.elt with
    | P_Abst(xs,t) -> out "λ%a, %a" args_list xs toplevel t
    | P_Prod(xs,b) -> out "Π%a, %a" args_list xs toplevel b
    | P_Impl(a,b) -> out "%a → %a" appl a toplevel b
    | P_LLet(x,xs,a,t,u) ->
        out "let %a%a%a ≔ %a in\n%a" ident x
          args_list xs annot a toplevel t toplevel u
    | _ -> out "%a" func t
  in
  toplevel ppf t

and annot : p_type option pp = fun ppf a ->
  match a with
  | Some(a) -> fprintf ppf " : %a" term a
  | None    -> ()

and args : p_args pp = fun ppf (ids,ao,b) ->
  let args = List.pp arg_ident " " in
  match (ao,b) with
  | (None   , false) -> fprintf ppf "%a" args ids
  | (None   , true ) -> fprintf ppf "{%a}" args ids
  | (Some(a), false) -> fprintf ppf "(%a : %a)" args ids term a
  | (Some(a), true ) -> fprintf ppf "{%a : %a}" args ids term a

and args_list : p_args list pp = fun ppf ->
  List.iter (fprintf ppf " %a" args)

let rule : string -> p_rule pp = fun kw ppf {elt=(l,r);_} ->
  fprintf ppf "%s %a ↪ %a" kw term l term r

let inductive : string -> p_inductive pp =
  let cons ppf (id,a) = fprintf ppf "\n| %a : %a" ident id term a in
  fun kw ppf {elt=(id,a,cs);_} ->
  fprintf ppf "%s %a : %a ≔%a" kw ident id term a (List.pp cons "") cs

let equiv : (p_term * p_term) pp = fun ppf (l, r) ->
  fprintf ppf "%a ≡ %a" term l term r

(** [p_unpack eqs] is [unpack eqs] on syntax-level equivalences [eqs]. *)
let rec p_unpack : p_term -> (p_term * p_term) list = fun eqs ->
  let id s = snd s.Pos.elt in
  match Syntax.p_get_args eqs with
  | ({elt=P_Iden(s, _); _}, [v; w]) ->
      if id s = "#cons" then
        match Syntax.p_get_args v with
        | ({elt=P_Iden(e, _); _}, [t; u]) when id e = "#equiv" ->
            (t, u) :: p_unpack w
        | _                                                         ->
            assert false (* Ill-formed term. *)
      else if id s = "#equiv" then [(v, w)] else
      assert false (* Ill-formed term. *)
  | _                               -> assert false (* Ill-formed term. *)

let unif_rule : p_rule pp = fun ppf {elt=(lhs,rhs);_} ->
  let lhs =
    match Syntax.p_get_args lhs with
    | (_, [t; u]) -> (t, u)
    | _           -> assert false
  in
  let eqs = p_unpack rhs in
  Format.fprintf ppf "%a ↪ %a" equiv lhs (List.pp equiv ", ") eqs

let proof_end : p_proof_end pp = fun ppf {elt;_} ->
  match elt with
  | P_proof_end   -> pp_print_string ppf "end"
  | P_proof_admit -> pp_print_string ppf "admit"
  | P_proof_abort -> pp_print_string ppf "abort"

let rw_patt : p_rw_patt pp = fun ppf p ->
  let out fmt = fprintf ppf fmt in
  match p.elt with
  | P_rw_Term(t)               -> out "%a" term t
  | P_rw_InTerm(t)             -> out "in %a" term t
  | P_rw_InIdInTerm(x,t)       -> out "in %a in %a" ident x term t
  | P_rw_IdInTerm(x,t)         -> out "%a in %a" ident x term t
  | P_rw_TermInIdInTerm(u,x,t) -> out "%a in %a in %a" term u ident x term t
  | P_rw_TermAsIdInTerm(u,x,t) -> out "%a as %a in %a" term u ident x term t

let assertion : p_assertion pp = fun ppf asrt ->
  match asrt with
  | P_assert_typing(t,a) -> fprintf ppf "%a : %a" term t term a
  | P_assert_conv(t,u)   -> fprintf ppf "%a ≡ %a" term t term u

let query : p_query pp = fun ppf q ->
  let out fmt = fprintf ppf fmt in
  match q.elt with
  | P_query_assert(true , asrt) -> out "assertnot %a" assertion asrt
  | P_query_assert(false, asrt) -> out "assert %a" assertion asrt
  | P_query_verbose(i) -> out "set verbose %i" i
  | P_query_debug(true ,s) -> out "set debug \"+%s\"" s
  | P_query_debug(false,s) -> out "set debug \"-%s\"" s
  | P_query_flag(s, b) ->
      out "set flag \"%s\" %s" s (if b then "on" else "oppf")
  | P_query_infer(t, _) -> out "type %a" term t
  | P_query_normalize(t, _) -> out "compute %a" term t
  | P_query_prover(s) -> out "set prover \"%s\"" s
  | P_query_prover_timeout(n) -> out "set prover_timeout %d" n
  | P_query_print(None) -> out "print"
  | P_query_print(Some s) -> out "print %a" qident s
  | P_query_proofterm -> out "proofterm"

let tactic : p_tactic pp = fun ppf t ->
  let out fmt = fprintf ppf fmt in
  begin match t.elt with
  | P_tac_refine(t) -> out "refine %a" term t
  | P_tac_intro(xs) -> out "intro %a" (List.pp arg_ident " ") xs
  | P_tac_apply(t) -> out "apply %a" term t
  | P_tac_simpl -> out "simpl"
  | P_tac_rewrite(b,p,t)     ->
      let dir ppf b = if not b then fprintf ppf " -" in
      let pat ppf p = fprintf ppf " [%a]" rw_patt p in
      out "rewrite%a%a%a" dir b (Option.pp pat) p term t
  | P_tac_refl -> out "reflexivity"
  | P_tac_sym -> out "symmetry"
  | P_tac_focus(i) -> out "focus %i" i
  | P_tac_why3(p) ->
      let prover ppf s = fprintf ppf " %s" s in
      out "why3%a" (Option.pp prover) p
  | P_tac_query(q) -> query ppf q
  | P_tac_fail -> out "fail"
  | P_tac_solve -> out "solve"
  end;
  out ";"

let command : p_command pp = fun ppf {elt;_} ->
  let out fmt = fprintf ppf fmt in
  begin match elt with
  | P_require(b,ms) ->
      let op = if b then " open" else "" in
      out "require%s %a" op (List.pp p_mod " ") ms
  | P_require_as(m,i) -> out "require %a as %a" p_mod m ident i
  | P_open(ms) -> out "open %a" (List.pp p_mod " ") ms
  | P_symbol{p_sym_mod;p_sym_nam;p_sym_arg;p_sym_typ;p_sym_trm;p_sym_prf
             ;p_sym_def} ->
    begin
      out "%asymbol %a%a"
        (List.pp modifier "") p_sym_mod
        ident p_sym_nam
        args_list p_sym_arg;
      Option.iter (out " : %a" term) p_sym_typ;
      if p_sym_def then out " ≔";
      Option.iter (out " %a" term) p_sym_trm;
      match p_sym_prf with
      | Some(ts,pe) ->
          let tac ppf = fprintf ppf "\n  %a" tactic in
          out "\nbegin%a\n%a" (List.pp tac "") ts proof_end pe
      | None -> ()
    end
  | P_rules [] -> assert false (* not possible *)
  | P_rules (r::rs) ->
      out "%a" (rule "rule") r;
      List.iter (out "%a" (rule "\nwith")) rs
  | P_inductive(_, _, []) -> assert false (* not possible *)
  | P_inductive(ms, xs, i::il) ->
      out "begin %a%a\n%a%a\nend"
        (List.pp modifier "") ms
        (List.pp args " ") xs
        (inductive "inductive") i
        (List.pp (inductive "\nwith") "") il
  | P_set(P_config_builtin(n,i)) ->
      out "set builtin %S ≔ %a" n qident i
  | P_set(P_config_unop(s,p,qid)) ->
      out "set prefix %f %S ≔ %a" p s qident qid
  | P_set(P_config_binop(s,a,p,qid)) ->
      let a =
        match a with
        | Pratter.Neither -> ""
        | Pratter.Left -> " left"
        | Pratter.Right -> " right"
      in
      out "set infix%s %f %S ≔ %a" a p s qident qid
  | P_set(P_config_unif_rule(ur)) ->
      out "set unif_rule %a" unif_rule ur
  | P_set(P_config_quant(qid)) ->
      out "set quantifier %a" qident qid
  | P_query(q) ->
     query ppf q
  end;
  out ";"

let ast : ast pp = fun ppf ->
  Stream.iter (fun c -> command ppf c; Format.pp_print_newline ppf ())

(** [beautify cmds] pretty-prints the commands [cmds] to standard output. *)
let beautify : ast -> unit = ast std_formatter
