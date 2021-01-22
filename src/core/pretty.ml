(** Pretty-printing the parser-level AST.

    This module defines functions that allow printing elements of syntax found
    in the parser-level abstract syntax. This is used, for example, to print a
    file in the Lambdapi syntax, given the AST obtained when parsing a file in
    the legacy (Dedukti) syntax. *)

open! Lplib
open Lplib.Base

open Console
open Pos
open Syntax

let string = Format.pp_print_string

let ident : ident pp = fun ff {pos; elt} ->
  if LpLexer.is_keyword elt then
    fatal pos "Identifier [%s] is a Lambdapi keyword." elt;
  string ff elt

let arg_ident : ident option pp = fun ff id ->
  match id with
  | Some(id) -> ident ff id
  | None     -> string ff "_"

let path_elt : Pos.popt -> (string * bool) pp = fun pos ff (s,b) ->
  if not b && LpLexer.is_keyword s then
    fatal pos "Module path member [%s] is a Lambdapi keyword." s;
  if b then Format.fprintf ff "{|%s|}" s else string ff s

let path : Pos.popt -> p_module_path pp = fun pos ->
  List.pp (path_elt pos) "."

let qident : qident pp = fun ff {elt=(path,id); pos} ->
  List.iter (Format.fprintf ff "%a." (path_elt pos)) path;
  ident ff (Pos.make pos id)

let modifier : p_modifier pp = fun ff {elt; _} ->
  match elt with
  | P_expo(e) -> Print.pp_expo ff e
  | P_mstrat(s) -> Print.pp_match_strat ff s
  | P_prop(p) -> Print.pp_prop ff p
  | P_opaq -> string ff "opaque "

let rec term : p_term pp = fun ff t ->
  let out fmt = Format.fprintf ff fmt in
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
  and atom ff t = pp `PAtom ff t
  and appl ff t = pp `PAppl ff t
  and func ff t = pp `PFunc ff t
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
  toplevel ff t

and annot : p_type option pp = fun ff a ->
  match a with
  | Some(a) -> Format.fprintf ff " : %a" term a
  | None    -> ()

and args : p_args pp = fun ff (ids,ao,b) ->
  let args = List.pp arg_ident " " in
  match (ao,b) with
  | (None   , false) -> Format.fprintf ff "%a" args ids
  | (None   , true ) -> Format.fprintf ff "{%a}" args ids
  | (Some(a), false) -> Format.fprintf ff "(%a : %a)" args ids term a
  | (Some(a), true ) -> Format.fprintf ff "{%a : %a}" args ids term a

and args_list : p_args list pp = fun ff ->
  List.iter (Format.fprintf ff " %a" args)

let rule : string -> p_rule pp = fun kw ff {elt=(l,r);_} ->
  Format.fprintf ff "%s %a ↪ %a" kw term l term r

let inductive : string -> p_inductive pp = fun kw ff {elt=(id,a,cs);_} ->
  let cons ff (id,a) = Format.fprintf ff "\n| %a : %a" ident id term a in
  Format.fprintf ff "%s %a : %a ≔%a" kw ident id term a (List.pp cons "") cs

let equiv : (p_term * p_term) pp = fun ff (l, r) ->
  Format.fprintf ff "%a ≡ %a" term l term r

let unif_rule : p_rule pp = fun ff {elt=(lhs,rhs);_} ->
  let lhs =
    match Syntax.p_get_args lhs with
    | (_, [t; u]) -> (t, u)
    | _           -> assert false
  in
  let eqs = Unif_rule.p_unpack rhs in
  Format.fprintf ff "%a ↪ %a" equiv lhs (List.pp equiv ", ") eqs

let proof_end : p_proof_end pp = fun ff {elt;_} ->
  match elt with
  | P_proof_end   -> string ff "end"
  | P_proof_admit -> string ff "admit"
  | P_proof_abort -> string ff "abort"

let rw_patt : p_rw_patt pp = fun ff p ->
  let out fmt = Format.fprintf ff fmt in
  match p with
  | P_rw_Term(t)               -> out "%a" term t
  | P_rw_InTerm(t)             -> out "in %a" term t
  | P_rw_InIdInTerm(x,t)       -> out "in %a in %a" ident x term t
  | P_rw_IdInTerm(x,t)         -> out "%a in %a" ident x term t
  | P_rw_TermInIdInTerm(u,x,t) -> out "%a in %a in %a" term u ident x term t
  | P_rw_TermAsIdInTerm(u,x,t) -> out "%a as %a in %a" term u ident x term t

let assertion : p_assertion pp = fun ff asrt ->
  let out fmt = Format.fprintf ff fmt in
  match asrt with
  | P_assert_typing(t,a) -> out "%a : %a" term t term a
  | P_assert_conv(t,u)   -> out "%a ≡ %a" term t term u

let query : p_query pp = fun ff q ->
  let out fmt = Format.fprintf ff fmt in
  match q.elt with
  | P_query_assert(true , asrt) -> out "assertnot %a" assertion asrt
  | P_query_assert(false, asrt) -> out "assert %a" assertion asrt
  | P_query_verbose(i) -> out "set verbose %i" i
  | P_query_debug(true ,s) -> out "set debug \"+%s\"" s
  | P_query_debug(false,s) -> out "set debug \"-%s\"" s
  | P_query_flag(s, b) ->
      out "set flag \"%s\" %s" s (if b then "on" else "off")
  | P_query_infer(t, _) -> out "type %a" term t
  | P_query_normalize(t, _) -> out "compute %a" term t
  | P_query_prover(s) -> out "set prover \"%s\"" s
  | P_query_prover_timeout(n) -> out "set prover_timeout %d" n
  | P_query_print(None) -> out "print"
  | P_query_print(Some s) -> out "print %a" qident s
  | P_query_proofterm -> out "proofterm"

let tactic : p_tactic pp = fun ff t ->
  let out fmt = Format.fprintf ff fmt in
  match t.elt with
  | P_tac_refine(t) -> out "refine %a" term t
  | P_tac_intro(xs) -> out "intro %a" (List.pp arg_ident " ") xs
  | P_tac_apply(t) -> out "apply %a" term t
  | P_tac_simpl -> out "simpl"
  | P_tac_rewrite(b,p,t)     ->
      let dir ff b = if not b then Format.fprintf ff " -" in
      let pat ff p = Format.fprintf ff " [%a]" rw_patt p.elt in
      out "rewrite%a%a%a" dir b (Option.pp pat) p term t
  | P_tac_refl -> out "reflexivity"
  | P_tac_sym -> out "symmetry"
  | P_tac_focus(i) -> out "focus %i" i
  | P_tac_why3(p) ->
      let prover ff s = Format.fprintf ff " %s" s in
      out "why3%a" (Option.pp prover) p
  | P_tac_query(q) -> query ff q
  | P_tac_fail -> out "fail"
  | P_tac_solve -> out "solve"

let command : p_command pp = fun ff cmd ->
  let out fmt = Format.fprintf ff fmt in
  match cmd.elt with
  | P_require(b,ps) ->
      let op = if b then " open" else "" in
      out "require%s %a" op (List.pp (path cmd.pos) " ") ps
  | P_require_as(p,{elt;pos}) ->
      out "require %a as %a" (path cmd.pos) p (path_elt pos) elt
  | P_open(ps) ->
      List.iter (out "open %a" (path cmd.pos)) ps
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
          out "\nbegin";
          List.iter (out "\n  %a" tactic) ts;
          out "\n%a" proof_end pe
      | None -> ()
    end
  | P_rules [] -> ()
  | P_rules (r::rs) ->
      out "%a" (rule "rule") r;
      List.iter (out "%a" (rule "\nwith")) rs
  | P_inductive(_, []) -> ()
  | P_inductive(ms, i::il) ->
      out "%a" (List.pp modifier "") ms;
      out "%a" (inductive "inductive") i;
      List.iter (out "%a" (inductive "\nwith")) il
  | P_set(P_config_builtin(n,i)) ->
      out "set builtin %S ≔ %a" n qident i
  | P_set(P_config_unop(unop)) ->
      let (s, p, qid) = unop in
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
     query ff q

let ast : ast pp = fun ff ->
  Stream.iter (fun c -> command ff c; Format.pp_print_newline ff ())

(** [beautify cmds] pretty-prints the commands [cmds] to standard output. *)
let beautify : ast -> unit = ast Format.std_formatter
