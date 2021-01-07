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

(** [is_keyword s] returns [true] if [s] is a keyword (defined by the lexer)
    in {!module:Lp_lexer}. *)
let is_keyword : string -> bool = fun s ->
  List.mem s
    [ "TYPE"
    ; "apply"
    ; "as"
    ; "assert"
    ; "assertnot"
    ; "assume"
    ; "builtin"
    ; "compute"
    ; "constant"
    ; "definition"
    ; "flag"
    ; "in"
    ; "inductive"
    ; "infix"
    ; "injective"
    ; "left"
    ; "let"
    ; "off"
    ; "on"
    ; "open"
    ; "prefix"
    ; "private"
    ; "proof"
    ; "protected"
    ; "prover"
    ; "prover_timeout"
    ; "qed"
    ; "refine"
    ; "refine"
    ; "reflexivity"
    ; "require"
    ; "rewrite"
    ; "right"
    ; "rule"
    ; "set"
    ; "sequential"
    ; "simpl"
    ; "symbol"
    ; "symmetry"
    ; "theorem"
    ; "type"
    ; "type"
    ; "unif_rule"
    ; "verbose"
    ; "why3"
    ; "with" ]
let string = Format.pp_print_string

let ident : ident pp = fun oc id ->
  if is_keyword id.elt then
    fatal id.pos "Identifier [%s] is a Lambdapi keyword." id.elt;
  string oc id.elt

let arg_ident : ident option pp = fun oc id ->
  match id with
  | Some(id) -> ident oc id
  | None     -> string oc "_"

let path_elt : Pos.popt -> (string * bool) pp = fun pos oc (s,b) ->
  if not b && is_keyword s then
    fatal pos "Module path member [%s] is a Lambdapi keyword." s;
  if b then Format.fprintf oc "{|%s|}" s else string oc s

let qident : qident pp = fun oc qid ->
  List.iter (Format.fprintf oc "%a." (path_elt qid.pos)) (fst qid.elt);
  ident oc (Pos.make qid.pos (snd qid.elt))

let path : Pos.popt -> p_module_path pp = fun pos ->
  List.pp (path_elt pos) "."

let modifier : p_modifier pp = fun oc {elt; _} ->
  match elt with
  | P_expo(e) -> Print.pp_expo oc e
  | P_mstrat(s) -> Print.pp_match_strat oc s
  | P_prop(p) -> Print.pp_prop oc p
  | P_opaq -> string oc "opaque "

let rec term : p_term pp = fun oc t ->
  let out fmt = Format.fprintf oc fmt in
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
    | (P_UnaO((u,_,_),t)   , _    ) -> out "(%s %a)" u atom t
    | (P_BinO(t,(b,_,_,_),u), _   ) -> out "(%a %s %a)" atom t b atom u
    (* We print minimal parentheses, and ignore the [Wrap] constructor. *)
    | (P_Wrap(t)           , _    ) -> out "%a" (pp p) t
    | (P_Expl(t)           , _    ) -> out "{%a}" func t
    | (_                   , _    ) -> out "(%a)" func t
  and atom oc t = pp `PAtom oc t
  and appl oc t = pp `PAppl oc t
  and func oc t = pp `PFunc oc t
  in
  let rec toplevel _ t =
    match t.elt with
    | P_Abst(xs,t) -> out "λ%a, %a" args_list xs toplevel t
    | P_Prod(xs,b) -> out "Π%a, %a" args_list xs toplevel b
    | P_Impl(a,b) -> out "%a → %a" appl a toplevel b
    | P_LLet(x,xs,a,t,u) ->
        out "@[<hov 2>let %a%a%a ≔ %a@] in %a" ident x
          args_list xs annot a toplevel t toplevel u
    | _ -> out "%a" func t
  in
  toplevel oc t

and annot : p_type option pp = fun oc a ->
  match a with
  | Some(a) -> Format.fprintf oc " :@ %a" term a
  | None    -> ()

and args : p_args pp = fun oc (ids,ao,b) ->
  let args = List.pp arg_ident " " in
  match (ao,b) with
  | (None   , false) -> Format.fprintf oc "%a" args ids
  | (None   , true ) -> Format.fprintf oc "{%a}" args ids
  | (Some(a), false) -> Format.fprintf oc "(%a : %a)" args ids term a
  | (Some(a), true ) -> Format.fprintf oc "{%a : %a}" args ids term a

and args_list : p_args list pp = fun oc ->
  List.iter (Format.fprintf oc " %a" args)

let rule : string -> p_rule pp = fun kw oc r ->
  let (lhs, rhs) = r.elt in
  Format.fprintf oc "@[<hov 3>%s %a ↪ %a@]@?" kw term lhs term rhs

let inductive : string -> p_inductive pp = fun kw oc i ->
  let (s, t, tl) = i.elt in
  Format.fprintf oc "@[<hov 2>]%s %a" kw ident s;
  Format.fprintf oc " :@ @[<hov>%a@] ≔@ \n  " term t;
  let cons oc (id,a) =
    Format.fprintf oc "%a:@ @[<hov>%a@]" ident id term a in
  List.pp cons "\n| " oc tl

let equi : (p_term * p_term) pp = fun oc (l, r) ->
  Format.fprintf oc "@[<hov 3>%a ≡ %a@]@?" term l term r

let unif_rule : p_rule pp = fun oc r ->
  let (lhs, rhs) = r.elt in
  let lhs =
    match Syntax.p_get_args lhs with
    | (_, [t; u]) -> (t, u)
    | _           -> assert false
  in
  let eqs = Unif_rule.p_unpack rhs in
  Format.fprintf oc "@[<hov 3>%a ↪ %a@]@?" equi lhs (List.pp equi ", ") eqs

let proof_end : p_proof_end pp = fun oc {elt;_} ->
  match elt with
  | P_proof_end   -> string oc "end"
  | P_proof_admit -> string oc "admit"
  | P_proof_abort -> string oc "abort"

let rw_patt : p_rw_patt pp = fun oc p ->
  let out fmt = Format.fprintf oc fmt in
  match p with
  | P_rw_Term(t)               -> out "%a" term t
  | P_rw_InTerm(t)             -> out "in %a" term t
  | P_rw_InIdInTerm(x,t)       -> out "in %a in %a" ident x term t
  | P_rw_IdInTerm(x,t)         -> out "%a in %a" ident x term t
  | P_rw_TermInIdInTerm(u,x,t) -> out "%a in %a in %a" term u
                                    ident x term t
  | P_rw_TermAsIdInTerm(u,x,t) -> out "%a as %a in %a" term u
                                    ident x term t

let assertion : p_assertion pp = fun oc asrt ->
  let out fmt = Format.fprintf oc fmt in
  match asrt with
  | P_assert_typing(t,a) -> out "%a : %a" term t term a
  | P_assert_conv(t,u)   -> out "%a ≡ %a" term t term u

let query : p_query pp = fun oc q ->
  let out fmt = Format.fprintf oc fmt in
  match q.elt with
  | P_query_assert(true , asrt) -> out "assertnot %a" assertion asrt
  | P_query_assert(false, asrt) -> out "assert %a" assertion asrt
  | P_query_verbose(i) -> out "set verbose %i" i
  | P_query_debug(true ,s) -> out "set debug \"+%s\"" s
  | P_query_debug(false,s) -> out "set debug \"-%s\"" s
  | P_query_flag(s, b) ->
      out "set flag \"%s\" %s" s (if b then "on" else "off")
  | P_query_infer(t, _) -> out "@[<hov 4>type %a@]" term t
  | P_query_normalize(t, _) -> out "@[<hov 2>compute@ %a@]" term t
  | P_query_prover(s) -> out "set prover \"%s\"" s
  | P_query_prover_timeout(n) -> out "set prover_timeout %d" n
  | P_query_print(None) -> out "print"
  | P_query_print(Some s) -> out "print %a" qident s
  | P_query_proofterm -> out "proofterm"

let tactic : p_tactic pp = fun oc t ->
  let out fmt = Format.fprintf oc fmt in
  match t.elt with
  | P_tac_refine(t) -> out "@[<hov 2>refine@ %a@]" term t
  | P_tac_intro(xs) -> out "intro %a" (List.pp arg_ident " ") xs
  | P_tac_apply(t) -> out "@[<hov 2>apply %a@]" term t
  | P_tac_simpl -> out "simpl"
  | P_tac_rewrite(b,p,t)     ->
      let dir oc b = if not b then Format.fprintf oc " -" in
      let pat oc p = Format.fprintf oc " [%a]@" rw_patt p.elt in
      out "@[<hov 2>rewrite%a%a%a@]" dir b (Option.pp pat) p term t
  | P_tac_refl -> out "reflexivity"
  | P_tac_sym -> out "symmetry"
  | P_tac_focus(i) -> out "focus %i" i
  | P_tac_why3(p) ->
      let prover oc s = Format.fprintf oc " %s" s in
      out "why3%a" (Option.pp prover) p
  | P_tac_query(q) -> query oc q
  | P_tac_fail -> out "fail"
  | P_tac_solve -> out "solve"

let command : p_command pp = fun oc cmd ->
  let out fmt = Format.fprintf oc fmt in
  match cmd.elt with
  | P_require(b,ps) ->
      let op = if b then " open" else "" in
      out "require%s %a" op (List.pp (path cmd.pos) " ") ps
  | P_require_as(p,i) ->
      out "require %a as %a" (path cmd.pos) p (path_elt i.pos) i.elt
  | P_open(ps) ->
      List.iter (out "open %a" (path cmd.pos)) ps
  | P_symbol{p_sym_mod;p_sym_nam;p_sym_arg;p_sym_typ;p_sym_trm;p_sym_prf;_} ->
    begin
      match (p_sym_trm,p_sym_prf) with
      | (Some _,_) | (_,Some _) ->
        out "@[<hov 2>%asymbol %a"
          (List.pp modifier "") p_sym_mod ident p_sym_nam;
        args_list oc p_sym_arg;
        Option.iter (out " : @[<hov>%a@]" term) p_sym_typ;
        Option.iter (out " ≔ @[<hov>%a@]@]" term) p_sym_trm;
        begin
          match p_sym_prf with
          | Some(ts,pe) ->
            out "proof@.";
            List.iter (out "  @[<hov>%a@]@." tactic) ts;
            out "%a" proof_end pe
          | None -> ()
        end
      | (None,None) ->
        let a =
          match p_sym_typ with
          | Some(a) -> a
          | None ->
              fatal cmd.pos
                "symbol declaration with no type and no definition"
        in
        out "@[<hov 2>%asymbol %a"
          (List.pp modifier "") p_sym_mod ident p_sym_nam;
        args_list oc p_sym_arg;
        out " :@ @[<hov>%a@]" term a
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
        | Assoc_none  -> ""
        | Assoc_left  -> " left"
        | Assoc_right -> " right"
      in
      out "set infix%s %f %S ≔ %a" a p s qident qid
  | P_set(P_config_unif_rule(ur)) ->
      out "set unif_rule %a" unif_rule ur
  | P_set(P_config_ident(id)) ->
      out "set declared %S" id
  | P_set(P_config_quant(qid)) ->
      out "set quantifier %a" qident qid
  | P_query(q) ->
     query oc q

let ast : ast pp = fun oc cs -> List.pp command "\n@." oc cs

(** [beautify cmds] pretty-prints the commands [cmds] to standard output. *)
let beautify : ast -> unit = ast Format.std_formatter
