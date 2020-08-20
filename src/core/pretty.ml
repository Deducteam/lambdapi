(** Pretty-printing the parser-level AST.

    This module defines functions that allow printing elements of syntax found
    in the parser-level abstract syntax. This is used, for example, to print a
    file in the Lambdapi syntax, given the AST obtained when parsing a file in
    the legacy (Dedukti) syntax. *)

open Extra
open Console
open Pos
open Syntax

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
        out "λ%a, " pp_p_args args;
        let fn (ids,_,_) = List.for_all ((=) None) ids in
        let ec = !empty_context in
        empty_context := ec && List.for_all fn args;
        out "%a" pp_func t;
        empty_context := ec
    | (P_Prod(args,b)      , PFunc) -> out "Π%a, %a" pp_p_args args pp_func b
    | (P_LLet(x,args,a,t,u), PFunc) ->
        out "@[<hov 2>let %a%a%a ≔@ %a@] in %a"
          pp_ident x pp_p_args args pp_p_annot a pp_func t pp_func u
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
  let rec pp_toplevel _ t =
    match t.elt with
    | P_Abst(args,t)       -> out "λ%a, %a" pp_p_args args pp_toplevel t
    | P_Prod(args,b)       -> out "Π%a, %a" pp_p_args args pp_toplevel b
    | P_Impl(a,b)          -> out "%a → %a" (pp PAppl) a pp_toplevel b
    | P_LLet(x,args,a,t,u) ->
        out "@[<hov 2>let %a%a%a ≔ %a@] in %a" pp_ident x
          pp_p_args args pp_p_annot a pp_toplevel t pp_toplevel u
    | _                    -> out "%a" (pp PFunc) t
  in
  pp_toplevel oc t

and pp_p_annot : p_type option pp = fun oc a ->
  match a with
  | Some(a) -> Format.fprintf oc " :@ %a" pp_p_term a
  | None    -> ()

and pp_p_arg : p_arg pp = fun oc (ids,ao,b) ->
  let pp_ids = List.pp pp_arg_ident " " in
  match (ao,b) with
  | (None   , false) -> Format.fprintf oc "%a" pp_ids ids
  | (None   , true ) -> Format.fprintf oc "{%a}" pp_ids ids
  | (Some(a), false) -> Format.fprintf oc "(%a : %a)" pp_ids ids pp_p_term a
  | (Some(a), true ) -> Format.fprintf oc "{%a : %a}" pp_ids ids pp_p_term a

and pp_p_args : p_arg list pp = fun oc ->
  List.iter (Format.fprintf oc " %a" pp_p_arg)

let pp_p_rule : bool -> p_rule pp = fun first oc r ->
  let (lhs, rhs) = r.elt in
  let kw = if first then "rule" else "with" in
  Format.fprintf oc "@[<hov 3>%s %a ↪ %a@]@?" kw pp_p_term lhs pp_p_term rhs

let pp_p_equi : (p_term * p_term) pp = fun oc (l, r) ->
  Format.fprintf oc "@[<hov 3>%a ≡ %a@]@?" pp_p_term l pp_p_term r

let pp_p_unif_rule : p_rule pp = fun oc r ->
  let (lhs, rhs) = r.elt in
  let lhs =
    match Syntax.p_get_args lhs with
    | (_, [t; u]) -> (t, u)
    | _           -> assert false
  in
  let eqs = Unif_rule.p_unpack rhs in
  let pp_sep : unit pp = fun oc () -> Format.fprintf oc ", " in
  Format.fprintf oc "@[<hov 3>%a ↪ %a@]@?"
    pp_p_equi lhs (Format.pp_print_list ~pp_sep pp_p_equi) eqs

let pp_p_proof_end : p_proof_end pp = fun oc e ->
  match e with
  | P_proof_qed   -> Format.pp_print_string oc "qed"
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

let pp_p_assertion : p_assertion pp = fun oc asrt ->
  let out fmt = Format.fprintf oc fmt in
  match asrt with
  | P_assert_typing(t,a) -> out "%a : %a" pp_p_term t pp_p_term a
  | P_assert_conv(t,u)   -> out "%a ≡ %a" pp_p_term t pp_p_term u

let pp_p_query : p_query pp = fun oc q ->
  let out fmt = Format.fprintf oc fmt in
  match q.elt with
  | P_query_assert(true , asrt)           ->
      out "assertnot %a" pp_p_assertion asrt
  | P_query_assert(false, asrt)           ->
      out "assert %a" pp_p_assertion asrt
  | P_query_verbose(i)                    ->
      out "set verbose %i" i
  | P_query_debug(true ,s)                ->
      out "set debug \"+%s\"" s
  | P_query_debug(false,s)                ->
      out "set debug \"-%s\"" s
  | P_query_flag(s, b)                    ->
      out "set flag \"%s\" %s" s (if b then "on" else "off")
  | P_query_infer(t, _)                   ->
      out "@[<hov 4>type %a@]" pp_p_term t
  | P_query_normalize(t, _)               ->
      out "@[<hov 2>compute@ %a@]" pp_p_term t
  | P_query_prover(s)                     ->
      out "set prover \"%s\"" s
  | P_query_prover_timeout(n)               ->
      out "set prover_timeout %d" n

let pp_p_tactic : p_tactic pp = fun oc t ->
  let out fmt = Format.fprintf oc fmt in
  match t.elt with
  | P_tac_refine(t)          -> out "@[<hov 2>refine@ %a@]" pp_p_term t
  | P_tac_intro(xs)          -> out "intro %a" (List.pp pp_arg_ident " ") xs
  | P_tac_apply(t)           -> out "@[<hov 2>apply %a@]" pp_p_term t
  | P_tac_simpl              -> out "simpl"
  | P_tac_rewrite(b,p,t)     ->
      let dir oc b = if not b then Format.fprintf oc " -" in
      let pat oc p = Format.fprintf oc " [%a]@" pp_p_rw_patt p.elt in
      out "@[<hov 2>rewrite%a%a%a@]" dir b (Option.pp pat) p pp_p_term t
  | P_tac_refl               -> out "reflexivity"
  | P_tac_sym                -> out "symmetry"
  | P_tac_focus(i)           -> out "focus %i" i
  | P_tac_print              -> out "print"
  | P_tac_proofterm          -> out "proofterm"
  | P_tac_why3(p)            ->
      let prover oc s = Format.fprintf oc " %s" s in
      out "why3%a" (Option.pp prover) p
  | P_tac_query(q)           -> pp_p_query oc q
  | P_tac_fail               -> out "fail"

let pp_command : p_command pp = fun oc cmd ->
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
      List.iter (out " %a" pp_p_arg) args;
      out " :@ @[<hov>%a@]" pp_p_term a
  | P_rules([])                     -> ()
  | P_rules(r::rs)                  ->
      out "%a" (pp_p_rule true) r;
      List.iter (out "%a" (pp_p_rule false)) rs
  | P_definition(ms,_,s,args,ao,t) ->
      out "@[<hov 2>%adefinition %a"
        (Format.pp_print_list pp_modifier) ms pp_ident s;
      List.iter (out " %a" pp_p_arg) args;
      Option.iter (out " : @[<hov>%a@]" pp_p_term) ao;
      out " ≔ @[<hov>%a@]@]" pp_p_term t
  | P_theorem(ms,st,ts,pe) ->
      let (s,args,a) = st.elt in
      out "@[<hov 2>%atheorem %a"
        (Format.pp_print_list pp_modifier) ms pp_ident s;
      List.iter (out " %a" pp_p_arg) args;
      out " : @[<2>%a@]@]@." pp_p_term a;
      out "proof@.";
      List.iter (out "  @[<hov>%a@]@." pp_p_tactic) ts;
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
      out "set unif_rule %a" pp_p_unif_rule ur
  | P_set(P_config_ident(id))       ->
      out "set declared %S" id
  | P_set(P_config_quant(qid))      ->
      out "set quantifier %a" pp_qident qid
  | P_query(q)                      ->
     pp_p_query oc q

let rec pp_ast : ast pp = fun oc cs ->
  match cs with
  | []    -> ()
  | [c]   -> Format.fprintf oc "%a@." pp_command c
  | c::cs -> Format.fprintf oc "%a\n@.%a" pp_command c pp_ast cs

(** Short synonym of [pp_p_term]. *)
let pp : p_term pp = pp_p_term

(** [beautify cmds] pretty-prints the commands [cmds] to standard output. *)
let beautify : ast -> unit =
  pp_ast Format.std_formatter
