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

type p_term = P_term.p_term
type p_type = P_term.p_type

let pp_ident : ident pp = fun oc id ->
  if Parser.KW.mem id.elt then
    fatal id.pos "Identifier [%s] is a Lambdapi keyword." id.elt;
  Format.pp_print_string oc id.elt

let pp_arg_ident : ident option pp = fun oc id ->
  match id with
  | Some(id) -> pp_ident oc id
  | None     -> Format.pp_print_string oc "_"

let pp_path_elt : Pos.popt -> (string * bool) pp = fun pos oc (s,b) ->
  if not b && Parser.KW.mem s then
    fatal pos "Module path member [%s] is a Lambdapi keyword." s;
  if b then Format.fprintf oc "{|%s|}" s else Format.pp_print_string oc s

let pp_qident : qident pp = fun oc qid ->
  List.iter (Format.fprintf oc "%a." (pp_path_elt qid.pos)) (fst qid.elt);
  pp_ident oc (Pos.make qid.pos (snd qid.elt))

let pp_path : Pos.popt -> p_module_path pp = fun pos ->
  List.pp (pp_path_elt pos) "."

let pp_modifier : p_modifier loc pp = fun oc {elt; _} ->
  match elt with
  | P_expo(Public) -> ()
  | P_expo(Protec) -> Format.pp_print_string oc "protected "
  | P_expo(Privat) -> Format.pp_print_string oc "private "
  | P_mstrat(Eager) -> ()
  | P_mstrat(Sequen) -> Format.pp_print_string oc "sequential "
  | P_prop(Defin) -> ()
  | P_prop(Const) -> Format.pp_print_string oc "constant "
  | P_prop(Injec) -> Format.pp_print_string oc "injective "

let rec pp_p_term : p_term pp = fun oc t ->
  let open Parser in (* for PAtom, PAppl and PFunc *)
  let open P_term in
  let out fmt = Format.fprintf oc fmt in
  let empty_context = ref true in
  let rec pp p _ t =
    let pp_env _ ar =
      match ar with
      | None -> ()
      | Some [||] when !empty_context -> ()
      | Some ar -> out "[%a]" (Array.pp (pp PFunc) "; ") ar
    in
    let pp_atom = pp PAtom in
    let pp_appl = pp PAppl in
    let pp_func = pp PFunc in
    match (t.elt, p) with
    | (P_Type              , _    ) -> out "TYPE"
    | (P_Iden(qid, false)  , _    ) -> out "%a" pp_qident qid
    | (P_Iden(qid, true )  , _    ) -> out "%a" pp_qident qid
    | (P_Wild              , _    ) -> out "_"
    | (P_Meta(x,ar)        , _    ) -> out "?%a%a" pp_ident x pp_env ar
    | (P_Patt(None   ,ar)  , _    ) -> out "$_%a" pp_env ar
    | (P_Patt(Some(x),ar)  , _    ) -> out "$%a%a" pp_ident x pp_env ar
    | (P_Appl(t,u)         , PAppl)
    | (P_Appl(t,u)         , PFunc) -> out "%a %a" pp_appl t pp_atom u
    | (P_Impl(a,b)         , PFunc) -> out "%a → %a" pp_appl a pp_func b
    | (P_Abst(args,t)      , PFunc) ->
        out "λ%a, " (pp_p_args pp_p_term) args;
        let fn (ids,_,_) = List.for_all ((=) None) ids in
        let ec = !empty_context in
        empty_context := ec && List.for_all fn args;
        out "%a" pp_func t;
        empty_context := ec
    | (P_Prod(args,b)      , PFunc) -> out "Π%a, %a" (pp_p_args pp_p_term) args pp_func b
    | (P_LLet(x,args,a,t,u), PFunc) ->
        out "@[<hov 2>let %a%a%a ≔@ %a@] in %a"
          pp_ident x (pp_p_args pp_p_term) args pp_p_annot a pp_func t pp_func u
    | (P_NLit(i)           , _    ) -> out "%i" i
    | (P_UnaO(u,t)         , _    ) ->
        let (u, _, _) = u in
        out "(%s %a)" u pp_atom t
    | (P_BinO(t,b,u)       , _    ) ->
        let (b, _, _, _) = b in
        out "(%a %s %a)" pp_atom t b pp_atom u
    (* We print minimal parentheses, and ignore the [Wrap] constructor. *)
    | (P_Wrap(t)           , _    ) -> out "%a" (pp p) t
    | (P_Expl(t)           , _    ) -> out "{%a}" pp_func t
    | (_                   , _    ) -> out "(%a)" pp_func t
  in
  let rec pp_toplevel _pp_term _ t =
    match t.elt with
    | P_Abst(args,t)       -> out "λ%a, %a" (pp_p_args _pp_term) args (pp_toplevel _pp_term) t
    | P_Prod(args,b)       -> out "Π%a, %a" (pp_p_args _pp_term) args (pp_toplevel _pp_term) b
    | P_Impl(a,b)          -> out "%a → %a" (pp PAppl) a (pp_toplevel _pp_term) b
    | P_LLet(x,args,a,t,u) ->
        out "@[<hov 2>let %a%a%a ≔ %a@] in %a" pp_ident x
          (pp_p_args _pp_term) args pp_p_annot a (pp_toplevel _pp_term) t (pp_toplevel _pp_term) u
    | _                    -> out "%a" (pp PFunc) t
  in
  pp_toplevel pp_p_term oc t

and pp_p_annot : p_type option pp = fun oc a ->
  match a with
  | Some(a) -> Format.fprintf oc " :@ %a" pp_p_term a
  | None    -> ()

and pp_p_arg : 'term. 'term pp -> 'term p_arg pp = fun _pp_term oc (ids,ao,b) ->
  let pp_ids = List.pp pp_arg_ident " " in
  match (ao,b) with
  | (None   , false) -> Format.fprintf oc "%a" pp_ids ids
  | (None   , true ) -> Format.fprintf oc "{%a}" pp_ids ids
  | (Some(a), false) -> Format.fprintf oc "(%a : %a)" pp_ids ids _pp_term a
  | (Some(a), true ) -> Format.fprintf oc "{%a : %a}" pp_ids ids _pp_term a

and pp_p_args : 'term. 'term pp -> 'term p_arg list pp = fun _pp_term oc ->
  List.iter (Format.fprintf oc " %a" (pp_p_arg _pp_term))

let pp_p_inductive : 'a. 'a pp -> string -> 'a p_inductive pp =
  fun _pp_term kw oc i ->
  let (s, t, tl) = i.elt in
  Format.fprintf oc "@[<hov 2>]%s %a" kw pp_ident s;
  Format.fprintf oc " :@ @[<hov>%a@] ≔@ \n  " _pp_term t;
  let pp_cons oc (id,a) =
    Format.fprintf oc "%a:@ @[<hov>%a@]" pp_ident id _pp_term a in
  List.pp pp_cons "\n| " oc tl

let pp_p_rule : 'term. 'term pp -> string -> 'term p_rule pp =
  fun _pp_term kw oc r ->
  let (lhs, rhs) = r.elt in
  Format.fprintf oc "@[<hov 3>%s %a ↪ %a@]@?" kw _pp_term lhs _pp_term rhs

let pp_p_equi : 'term. 'term pp -> ('term * 'term) pp = fun _pp_term oc (l, r) ->
  Format.fprintf oc "@[<hov 3>%a ≡ %a@]@?" _pp_term l _pp_term r

let pp_p_unif_rule :
  'term.
  ('term -> 'term * 'term list) ->
  ('term -> ('term * 'term) list) ->
  'term pp-> 'term p_rule pp = fun get_args unpack _pp_term oc r ->
  let (lhs, rhs) = r.elt in
  let lhs =
    match get_args lhs with
    | (_, [t; u]) -> (t, u)
    | _           -> assert false
  in
  let eqs = unpack rhs in
  let pp_sep : unit pp = fun oc () -> Format.fprintf oc ", " in
  Format.fprintf oc "@[<hov 3>%a ↪ %a@]@?"
    (pp_p_equi _pp_term) lhs (Format.pp_print_list ~pp_sep (pp_p_equi _pp_term)) eqs

let pp_p_proof_end : p_proof_end pp = fun oc e ->
  match e with
  | P_proof_qed   -> Format.pp_print_string oc "qed"
  | P_proof_admit -> Format.pp_print_string oc "admit"
  | P_proof_abort -> Format.pp_print_string oc "abort"

let pp_p_rw_patt : 'term. 'term pp -> 'term p_rw_patt pp = fun _pp_term oc p ->
  let out fmt = Format.fprintf oc fmt in
  match p with
  | P_rw_Term(t)               -> out "%a" _pp_term t
  | P_rw_InTerm(t)             -> out "in %a" _pp_term t
  | P_rw_InIdInTerm(x,t)       -> out "in %a in %a" pp_ident x _pp_term t
  | P_rw_IdInTerm(x,t)         -> out "%a in %a" pp_ident x _pp_term t
  | P_rw_TermInIdInTerm(u,x,t) -> out "%a in %a in %a" _pp_term u
                                    pp_ident x _pp_term t
  | P_rw_TermAsIdInTerm(u,x,t) -> out "%a as %a in %a" _pp_term u
                                    pp_ident x _pp_term t

let pp_p_assertion : 'term. 'term pp -> 'term p_assertion pp = fun _pp_term oc asrt ->
  let out fmt = Format.fprintf oc fmt in
  match asrt with
  | P_assert_typing(t,a) -> out "%a : %a" _pp_term t _pp_term a
  | P_assert_conv(t,u)   -> out "%a ≡ %a" _pp_term t _pp_term u

let pp_p_query : 'term. 'term pp -> 'term p_query pp = fun _pp_term oc q ->
  let out fmt = Format.fprintf oc fmt in
  match q.elt with
  | P_query_assert(true , asrt)           ->
      out "assertnot %a" (pp_p_assertion _pp_term) asrt
  | P_query_assert(false, asrt)           ->
      out "assert %a" (pp_p_assertion _pp_term) asrt
  | P_query_verbose(i)                    ->
      out "set verbose %i" i
  | P_query_debug(true ,s)                ->
      out "set debug \"+%s\"" s
  | P_query_debug(false,s)                ->
      out "set debug \"-%s\"" s
  | P_query_flag(s, b)                    ->
      out "set flag \"%s\" %s" s (if b then "on" else "off")
  | P_query_infer(t, _)                   ->
      out "@[<hov 4>type %a@]" _pp_term t
  | P_query_normalize(t, _)               ->
      out "@[<hov 2>compute@ %a@]" _pp_term t
  | P_query_prover(s)                     ->
      out "set prover \"%s\"" s
  | P_query_prover_timeout(n)               ->
      out "set prover_timeout %d" n

let pp_p_tactic : 'term. 'term pp -> 'term p_tactic pp = fun _pp_term oc t ->
  let out fmt = Format.fprintf oc fmt in
  match t.elt with
  | P_tac_refine(t)          -> out "@[<hov 2>refine@ %a@]" _pp_term t
  | P_tac_intro(xs)          -> out "intro %a" (List.pp pp_arg_ident " ") xs
  | P_tac_apply(t)           -> out "@[<hov 2>apply %a@]" _pp_term t
  | P_tac_simpl              -> out "simpl"
  | P_tac_rewrite(b,p,t)     ->
      let dir oc b = if not b then Format.fprintf oc " -" in
      let pat oc p = Format.fprintf oc " [%a]@" (pp_p_rw_patt _pp_term) p.elt in
      out "@[<hov 2>rewrite%a%a%a@]" dir b (Option.pp pat) p _pp_term t
  | P_tac_refl               -> out "reflexivity"
  | P_tac_sym                -> out "symmetry"
  | P_tac_focus(i)           -> out "focus %i" i
  | P_tac_print              -> out "print"
  | P_tac_proofterm          -> out "proofterm"
  | P_tac_why3(p)            ->
      let prover oc s = Format.fprintf oc " %s" s in
      out "why3%a" (Option.pp prover) p
  | P_tac_query(q)           -> (pp_p_query _pp_term) oc q
  | P_tac_fail               -> out "fail"

let pp_command : 'term.
  ('term -> 'term * 'term list) ->
  ('term -> ('term * 'term) list) ->
  'term pp -> 'term p_command pp = fun _get_args _unpack _pp_term oc cmd ->
  let out fmt = Format.fprintf oc fmt in
  match cmd.elt with
  | P_require(b,ps)             ->
      let op = if b then " open" else "" in
      out "require%s %a" op (List.pp (pp_path cmd.pos) " ") ps
  | P_require_as(p,i)               ->
      out "require %a as %a" (pp_path cmd.pos) p (pp_path_elt i.pos) i.elt
  | P_open(ps)                      ->
      List.iter (out "open %a" (pp_path cmd.pos)) ps
  | P_symbol(ms,s,args,a) ->
      out "@[<hov 2>%asymbol %a"
        (Format.pp_print_list pp_modifier) ms pp_ident s;
      List.iter (out " %a" (pp_p_arg _pp_term)) args;
      out " :@ @[<hov>%a@]" _pp_term a
  | P_rules([])                     -> ()
  | P_rules(r::rs)                  ->
      out "%a" (pp_p_rule _pp_term "rule") r;
      List.iter (out "%a" (pp_p_rule _pp_term "with")) rs
  | P_definition(ms,_,s,args,ao,t) ->
      out "@[<hov 2>%adefinition %a"
        (Format.pp_print_list pp_modifier) ms pp_ident s;
      List.iter (out " %a" (pp_p_arg _pp_term)) args;
      Option.iter (out " : @[<hov>%a@]" _pp_term) ao;
      out " ≔ @[<hov>%a@]@]" _pp_term t
  | P_inductive(_, []) -> ()
  | P_inductive(ms, i::il) ->
      out "%a" (Format.pp_print_list pp_modifier) ms;
      out "%a" (pp_p_inductive _pp_term "inductive") i;
      List.iter (out "%a" (pp_p_inductive _pp_term "with")) il
  | P_theorem(ms,st,ts,pe) ->
      let (s,args,a) = st.elt in
      out "@[<hov 2>%atheorem %a"
        (Format.pp_print_list pp_modifier) ms pp_ident s;
      List.iter (out " %a" (pp_p_arg _pp_term)) args;
      out " : @[<2>%a@]@]@." _pp_term a;
      out "proof@.";
      List.iter (out "  @[<hov>%a@]@." (pp_p_tactic _pp_term)) ts;
      out "%a" pp_p_proof_end pe.elt
  | P_set(P_config_builtin(n,i))    ->
      out "set builtin %S ≔ %a" n pp_qident i
  | P_set(P_config_unop(unop))      ->
      let (s, p, qid) = unop in
      out "set prefix %f %S ≔ %a" p s pp_qident qid
  | P_set(P_config_binop(binop))    ->
      let (s, a, p, qid) = binop in
      let a =
        match a with
        | Assoc_none  -> ""
        | Assoc_left  -> " left"
        | Assoc_right -> " right"
      in
      out "set infix%s %f %S ≔ %a" a p s pp_qident qid
  | P_set(P_config_unif_rule(ur))   ->
      out "set unif_rule %a" (pp_p_unif_rule _get_args _unpack _pp_term) ur
  | P_set(P_config_ident(id))       ->
      out "set declared %S" id
  | P_set(P_config_quant(qid))      ->
      out "set quantifier %a" pp_qident qid
  | P_query(q)                      ->
     pp_p_query _pp_term oc q

let pp_parser_command : p_term p_command pp =
  pp_command P_term.p_get_args Unif_rule.p_unpack pp_p_term

let pp_ast_command : Terms.term p_command pp =
  pp_command Basics.get_args Unif_rule.unpack Print.pp_term

let rec pp_ast : p_term ast pp = fun oc cs ->
  match cs with
  | []    -> ()
  | [c]   -> Format.fprintf oc "%a@." pp_parser_command c
  | c::cs ->
    Format.fprintf oc "%a\n@.%a" pp_parser_command c pp_ast cs

(** Short synonym of [pp_p_term]. *)
let pp : p_term pp = pp_p_term

(** [beautify cmds] pretty-prints the commands [cmds] to standard output. *)
let beautify : p_term ast -> unit =
  pp_ast Format.std_formatter
