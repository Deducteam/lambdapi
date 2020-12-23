(** Pretty-printing the parser-level AST.

    This module defines functions that allow printing elements of syntax found
    in the parser-level abstract syntax. The module provides a functor that
    allows to print abstract syntax trees parametrised by terms and rewrite
    rules. It is used in conjunction with the {!module:P_terms} to print an
    AST parsed from the legacy (Dedukti) syntax. *)

open! Lplib
open Lplib.Base

open Console
open Pos
open Syntax

let string = Format.pp_print_string

let ident : ident pp = fun oc id ->
  if KW.mem id.elt then
    fatal id.pos "Identifier [%s] is a Lambdapi keyword." id.elt;
  string oc id.elt

let arg_ident : ident option pp = fun oc id ->
  match id with
  | Some(id) -> ident oc id
  | None     -> string oc "_"

let path_elt : Pos.popt -> (string * bool) pp = fun pos oc (s,b) ->
  if not b && KW.mem s then
    fatal pos "Module path member [%s] is a Lambdapi keyword." s;
  if b then Format.fprintf oc "{|%s|}" s else string oc s

let qident : qident pp = fun oc qid ->
  List.iter (Format.fprintf oc "%a." (path_elt qid.pos)) (fst qid.elt);
  ident oc (Pos.make qid.pos (snd qid.elt))

let path : Pos.popt -> p_module_path pp = fun pos ->
  List.pp (path_elt pos) "."

let expo : Terms.expo pp = fun oc e ->
  match e with
  | Public -> ()
  | Protec -> Format.fprintf oc "protected "
  | Privat -> Format.fprintf oc "private "

let match_strat : Terms.match_strat pp = fun oc s ->
  match s with
  | Sequen -> Format.fprintf oc "sequential "
  | Eager -> ()

let prop : Terms.prop pp = fun oc p ->
  match p with
  | Defin -> ()
  | Const -> Format.fprintf oc "constant "
  | Injec -> Format.fprintf oc "injective "

let modifier : p_modifier pp = fun oc {elt; _} ->
  match elt with
  | P_expo(e) -> expo oc e
  | P_mstrat(s) -> match_strat oc s
  | P_prop(p) -> prop oc p
  | P_opaq -> string oc "opaque "

let proof_end : p_proof_end pp = fun oc {elt;_} ->
  match elt with
  | P_proof_end   -> string oc "end"
  | P_proof_admit -> string oc "admit"
  | P_proof_abort -> string oc "abort"

(** [Make(T)(R)] contains a set of printing functions for terms specified by
    module of printable terms [T] and printable rewrite rules [R]. *)
module Make (T: PP)(R: PP) = struct

  let annot : T.t option pp = fun oc a ->
    match a with
    | Some(a) -> Format.fprintf oc " :@ %a" T.pp a
    | None    -> ()

  let args : T.t p_args pp = fun oc (ids,ao,b) ->
    let pp_ids = List.pp arg_ident " " in
    match (ao,b) with
    | (None   , false) -> Format.fprintf oc "%a" pp_ids ids
    | (None   , true ) -> Format.fprintf oc "{%a}" pp_ids ids
    | (Some(a), false) -> Format.fprintf oc "(%a : %a)" pp_ids ids T.pp a
    | (Some(a), true ) -> Format.fprintf oc "{%a : %a}" pp_ids ids T.pp a

  let args_list : T.t p_args list pp = fun oc ->
    List.iter (Format.fprintf oc " %a" args)

  let inductive : string -> T.t p_inductive pp = fun kw oc i ->
    let (s, t, tl) = i.elt in
    Format.fprintf oc "@[<hov 2>]%s %a" kw ident s;
    Format.fprintf oc " :@ @[<hov>%a@] ≔@ \n  " T.pp t;
    let pp_cons oc (id,a) =
      Format.fprintf oc "%a:@ @[<hov>%a@]" ident id T.pp a in
    List.pp pp_cons "\n| " oc tl

  let equi : (T.t * T.t) pp = fun oc (l, r) ->
    Format.fprintf oc "@[<hov 3>%a ≡ %a@]@?" T.pp l T.pp r

  let rw_patt : T.t p_rw_patt pp = fun oc p ->
    let out fmt = Format.fprintf oc fmt in
    match p with
    | P_rw_Term(t)               -> out "%a" T.pp t
    | P_rw_InTerm(t)             -> out "in %a" T.pp t
    | P_rw_InIdInTerm(x,t)       -> out "in %a in %a" ident x T.pp t
    | P_rw_IdInTerm(x,t)         -> out "%a in %a" ident x T.pp t
    | P_rw_TermInIdInTerm(u,x,t) -> out "%a in %a in %a" T.pp u
                                      ident x T.pp t
    | P_rw_TermAsIdInTerm(u,x,t) -> out "%a as %a in %a" T.pp u
                                      ident x T.pp t

  let assertion : T.t p_assertion pp = fun oc asrt ->
    let out fmt = Format.fprintf oc fmt in
    match asrt with
    | P_assert_typing(t,a) -> out "%a : %a" T.pp t T.pp a
    | P_assert_conv(t,u)   -> out "%a ≡ %a" T.pp t T.pp u

  let query : T.t p_query pp = fun oc q ->
    let out fmt = Format.fprintf oc fmt in
    match q.elt with
    | P_query_assert(true , asrt) -> out "assertnot %a" assertion asrt
    | P_query_assert(false, asrt) -> out "assert %a" assertion asrt
    | P_query_verbose(i) -> out "set verbose %i" i
    | P_query_debug(true ,s) -> out "set debug \"+%s\"" s
    | P_query_debug(false,s) -> out "set debug \"-%s\"" s
    | P_query_flag(s, b) ->
        out "set flag \"%s\" %s" s (if b then "on" else "off")
    | P_query_infer(t, _) -> out "@[<hov 4>type %a@]" T.pp t
    | P_query_normalize(t, _) -> out "@[<hov 2>compute@ %a@]" T.pp t
    | P_query_prover(s) -> out "set prover \"%s\"" s
    | P_query_prover_timeout(n) -> out "set prover_timeout %d" n
    | P_query_print(None) -> out "print"
    | P_query_print(Some s) -> out "print %a" qident s
    | P_query_proofterm -> out "proofterm"

  let tactic : T.t p_tactic pp = fun oc t ->
    let out fmt = Format.fprintf oc fmt in
    match t.elt with
    | P_tac_refine(t)          -> out "@[<hov 2>refine@ %a@]" T.pp t
    | P_tac_intro(xs)          -> out "intro %a" (List.pp arg_ident " ") xs
    | P_tac_apply(t)           -> out "@[<hov 2>apply %a@]" T.pp t
    | P_tac_simpl              -> out "simpl"
    | P_tac_rewrite(b,p,t)     ->
        let dir oc b = if not b then Format.fprintf oc " -" in
        let pat oc p = Format.fprintf oc " [%a]@" rw_patt p.elt in
        out "@[<hov 2>rewrite%a%a%a@]" dir b (Option.pp pat) p T.pp t
    | P_tac_refl               -> out "reflexivity"
    | P_tac_sym                -> out "symmetry"
    | P_tac_focus(i)           -> out "focus %i" i
    | P_tac_why3(p)            ->
        let prover oc s = Format.fprintf oc " %s" s in
        out "why3%a" (Option.pp prover) p
    | P_tac_query(q)           -> query oc q
    | P_tac_fail               -> out "fail"
    | P_tac_solve              -> out "solve"

  let command : (T.t, R.t) p_command pp = fun oc cmd ->
    let out fmt = Format.fprintf oc fmt in
    match cmd.elt with
    | P_require(b,ps)             ->
        let op = if b then " open" else "" in
        out "require%s %a" op (List.pp (path cmd.pos) " ") ps
    | P_require_as(p,i)               ->
        out "require %a as %a" (path cmd.pos) p (path_elt i.pos) i.elt
    | P_open(ps)                      ->
        List.iter (out "open %a" (path cmd.pos)) ps
    | P_symbol{p_sym_mod;p_sym_nam;p_sym_arg;p_sym_typ;p_sym_trm;p_sym_prf;_}
                                      ->
      begin
        match (p_sym_trm,p_sym_prf) with
        | (Some _,_) | (_,Some _) ->
          out "@[<hov 2>%asymbol %a"
            (List.pp modifier " ") p_sym_mod ident p_sym_nam;
          args_list oc p_sym_arg;
          Option.iter (out " : @[<hov>%a@]" T.pp) p_sym_typ;
          Option.iter (out " ≔ @[<hov>%a@]@]" T.pp) p_sym_trm;
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
          out " :@ @[<hov>%a@]" T.pp a
      end
    | P_rules([])                     -> ()
    | P_rules(r::rs)                  ->
        out "first %a" R.pp r;
        List.iter (out "with %a" R.pp) rs
    | P_inductive(_, []) -> ()
    | P_inductive(ms, i::il) ->
        out "%a" (Format.pp_print_list modifier) ms;
        out "%a" (inductive "inductive") i;
        List.iter (out "%a" (inductive "\nwith")) il;
    | P_set(P_config_builtin(n,i))    ->
        out "set builtin %S ≔ %a" n qident i
    | P_set(P_config_unop(unop))      ->
        let (s, p, qid) = unop in
        out "set prefix %f %S ≔ %a" p s qident qid
    | P_set(P_config_binop(binop))    ->
        let (s, a, p, qid) = binop in
        let a =
          match a with
          | Assoc_none  -> ""
          | Assoc_left  -> " left"
          | Assoc_right -> " right"
        in
        out "set infix%s %f %S ≔ %a" a p s qident qid
    | P_set(P_config_unif_rule(ur))   -> R.pp oc ur
    | P_set(P_config_ident(id))       ->
        out "set declared %S" id
    | P_set(P_config_quant(qid))      ->
        out "set quantifier %a" qident qid
    | P_query(q)                      -> query oc q

  (** [pp_ast oc ast] pretty prints abstract syntax tree [ast] to formatter
      [oc]. *)
  let ast : (T.t, R.t) ast pp = List.pp command "\n@."
end
