(** Pretty-printing the parser-level AST. *)

open Extra
open Files
open Pos
open Syntax

let pp_ident : ident pp = fun oc id ->
  Format.pp_print_string oc id.elt

let pp_qident : qident pp = fun oc qid ->
  match qid.elt with
  | ([], id) -> Format.pp_print_string oc id
  | (mp, id) -> List.iter (Format.fprintf oc "%s.") mp;
                Format.pp_print_string oc id

let pp_symtag : symtag pp = fun oc tag ->
  match tag with
  | Sym_const -> Format.pp_print_string oc "const"
  | Sym_inj   -> Format.pp_print_string oc "injective"

let rec pp_p_term : p_term pp = fun oc t ->
  let open Parser in
  let out fmt = Format.fprintf oc fmt in
  let rec pp p _ t =
    let pp_env _ ar =
      if Array.length ar > 0 then out "[%a]" (Array.pp (pp PFunc) ", ") ar
    in
    match (t.elt, p) with
    | (P_Type            , _    ) -> out "TYPE"
    | (P_Vari(qid)       , _    ) -> out "%a" pp_qident qid
    | (P_Wild            , _    ) -> out "_"
    | (P_Meta(x,ar)      , _    ) -> out "?%a%a" pp_ident x pp_env ar
    | (P_Patt(x,ar)      , _    ) -> out "&%a%a" pp_ident x pp_env ar
    | (P_Appl(t,u)       , PAppl)
    | (P_Appl(t,u)       , PFunc) -> out "%a %a" (pp PAppl) t (pp PAtom) u
    | (P_Impl(a,b)       , PFunc) -> out "%a ⇒ %a" (pp PAppl) a (pp PFunc) b
    | (P_Abst(args,t)    , PFunc) -> out "λ%a, %a" (List.pp pp_p_arg " ")
                                       args (pp PFunc) t
    | (P_Prod(args,b)    , PFunc) -> out "∀%a, %a" (List.pp pp_p_arg " ")
                                       args (pp PFunc) b
    | (P_LLet(x,args,t,u), PFunc) -> out "let %a" pp_ident x;
                                     List.iter (out " %a" pp_p_arg) args;
                                     out " = %a" (pp PFunc) t;
                                     out " in %a" (pp PFunc) u
    | (P_NLit(i)         , _    ) -> out "%i" i
    | (_                 , _    ) -> out "(%a)" (pp PFunc) t
  in
  pp PFunc oc t

and pp_p_arg : p_arg pp = fun oc (id,ao) ->
  match ao with
  | None    -> Format.pp_print_string oc id.elt
  | Some(a) -> Format.fprintf oc "(%s : %a)" id.elt pp_p_term a

let pp_p_rule : p_rule pp = fun oc r ->
  let (lhs, rhs) = r.elt in
  Format.fprintf oc "rule %a → %a" pp_p_term lhs pp_p_term rhs

let pp_p_proof_end : p_proof_end pp = fun oc e ->
  match e with
  | P_proof_QED   -> Format.pp_print_string oc "qed"
  | P_proof_admit -> Format.pp_print_string oc "admit"
  | P_proof_abort -> Format.pp_print_string oc "abort"

let pp_p_rw_patt : p_rw_patt pp = fun oc p ->
  let out fmt = Format.fprintf oc fmt in
  match p with
  | P_rw_Term(t)               -> out "%a" pp_p_term t
  | P_rw_InTerm(t)             -> out "in %a" pp_p_term t
  | P_rw_InIdInTerm(x,t)       -> out "in %a in %a" pp_ident x pp_p_term t
  | P_rw_IdInTerm(x,t)         -> out "%a in %a" pp_ident x pp_p_term t
  | P_rw_TermInIdInTerm(u,x,t) -> out "%a in %a in %a" pp_p_term u
                                    pp_ident x pp_p_term t
  | P_rw_TermAsIdInTerm(u,x,t) -> out "%a as %a in %a" pp_p_term u
                                    pp_ident x pp_p_term t

let pp_p_tactic : p_tactic pp = fun oc t ->
  let out fmt = Format.fprintf oc fmt in
  match t.elt with
  | P_tac_refine(t)          -> out "refine %a" pp_p_term t
  | P_tac_intro(xs)          -> out "intro %a" (List.pp pp_ident " ") xs
  | P_tac_apply(t)           -> out "apply %a" pp_p_term t
  | P_tac_simpl              -> out "simpl"
  | P_tac_rewrite(None   ,t) -> out "rewrite %a" pp_p_term t
  | P_tac_rewrite(Some(p),t) -> out "rewrite [%a] %a"
                                  pp_p_rw_patt p.elt pp_p_term t
  | P_tac_refl               -> out "reflexivity"
  | P_tac_sym                -> out "symmetry"
  | P_tac_focus(i)           -> out "focus %i" i
  | P_tac_print              -> out "print"
  | P_tac_proofterm          -> out "proofterm"

let pp_p_assertion : p_assertion pp = fun oc asrt ->
  let out fmt = Format.fprintf oc fmt in
  match asrt with
  | P_assert_typing(t,a) -> out "%a : %a" pp_p_term t pp_p_term a
  | P_assert_conv(t,u)   -> out "%a ≡ %a" pp_p_term t pp_p_term u

let pp_command : command pp = fun oc cmd ->
  let out fmt = Format.fprintf oc fmt in
  match cmd.elt with
  | P_require(m, P_require_default) ->
      out "require %a" pp_path m
  | P_require(m, P_require_open   ) ->
      out "require open %a" pp_path m
  | P_require(m, P_require_as(i)  ) ->
      out "require %a as %s" pp_path m i.elt
  | P_open(m)                       ->
      out "open %a" pp_path m
  | P_symbol(tags,s,a)              ->
      out "symbol";
      List.iter (out " %a" pp_symtag) tags;
      out " %s : %a" s.elt pp_p_term a
  | P_rules(rs)                     ->
      List.pp pp_p_rule "\n" oc rs
  | P_definition(_,s,args,ao,t)     ->
      out "definition %s" s.elt;
      List.iter (out " %a" pp_p_arg) args;
      Option.iter (out " : %a" pp_p_term) ao;
      out " ≔\n  %a" pp_p_term t
  | P_theorem(s,a,ts,e)             ->
      out "theorem %s : %a\nproof\n" s.elt pp_p_term a;
      List.iter (out "  %a\n" pp_p_tactic) ts;
      pp_p_proof_end oc e
  | P_assert(mf, asrt)              ->
      out "assert%s %a" (if mf then "not" else "") pp_p_assertion asrt
  | P_set(P_config_verbose(i)  )    ->
      out "set verbose %i" i
  | P_set(P_config_debug(b,s)  )    ->
      out "set debug \"%c%s\"" (if b then '+' else '-') s
  | P_set(P_config_builtin(n,i))    ->
      out "set builtin %S ≔ %a" n pp_qident i
  | P_infer(t, _)                   ->
      out "infer %a" pp_p_term t
  | P_normalize(t, _)               ->
      out "normalize %a" pp_p_term t

let pp_ast : ast pp =
  List.pp pp_command "\n\n"

(** [beautify cmds] pretty-prints the commands [cmds] to standard output. *)
let beautify : ast -> unit =
  pp_ast Format.std_formatter
