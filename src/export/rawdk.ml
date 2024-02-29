(** Translate the parser-level AST to Dedukti. *)

open Lplib open Base open Extra
open Common open Pos open Error
open Parsing open Syntax
open Format
open Core open Eval

let raw_ident : string pp = string

let ident : p_ident pp = fun ppf {elt;_} -> raw_ident ppf elt

let param_id : p_ident option pp = fun ppf idopt ->
  match idopt with
  | Some id -> ident ppf id
  | None     -> out ppf "_"

let raw_path : Path.t pp = List.pp string "."

let path : p_path pp = fun ppf {elt;_} -> raw_path ppf elt

let qident : p_qident pp = fun ppf ({elt=(mp,s);pos} as qid) ->
  match mp with
  | [] -> raw_ident ppf s
  | [_;m] -> out ppf "%a.%a" raw_ident m raw_ident s
  | _ -> fatal pos "Cannot be translated: %a.@." Pretty.qident qid

let rec term : p_term pp = fun ppf t ->
  match t.elt with
  | P_Meta _ -> assert false
  | P_Patt(id,ts) -> out ppf "%a%a" param_id id (Option.pp terms) ts;
  | P_Expl u -> out ppf "(%a)" term u
  | P_Type -> out ppf "Type"
  | P_Wild -> out ppf "_"
  | P_NLit i -> string ppf i
  | P_Iden(qid,_) -> qident ppf qid
  | P_Arro(u,v) -> out ppf "(%a -> %a)" term u term v
  | P_Abst(xs,u) -> out ppf "(%a%a)" abs xs term u
  | P_Prod(xs,u) -> out ppf "(%a%a)" prod xs term u
  | P_LLet(x,xs,None,u,v) ->
      out ppf "((%a => %a) (%a%a))" ident x term v abs xs term u
  | P_LLet(x,xs,Some a,u,v) ->
      out ppf "((%a : %a%a => %a) (%a%a))"
        ident x prod xs term a term v abs xs term u
  | P_Wrap u -> out ppf "(%a)" term u
  | P_Appl(u,v) -> out ppf "(%a %a)" term u term v

and terms : p_term array pp = fun ppf -> Array.iter (out ppf " %a" term)

and param : p_term option -> string -> p_ident option pp =
  fun a sep ppf id -> out ppf "%a%a%s" param_id id typopt a sep

and params : string -> p_params pp = fun sep ppf (ids,a,_) ->
  List.iter (out ppf "%a" (param a sep)) ids

and params_list : string -> p_params list pp = fun sep ppf ->
  List.iter (out ppf "%a" (params sep))

and abs : p_params list pp = fun ppf -> params_list " => " ppf

and prod : p_params list pp = fun ppf -> params_list " -> " ppf

and typopt : p_term option pp = fun ppf t ->
  Option.iter (out ppf " : %a" term) t

let bool : bool pp = fun ppf b -> if not b then out ppf "NOT"

let assertion : (bool * p_assertion) pp = fun ppf (b,a) ->
  match a with
  | P_assert_typing(t,u) -> out ppf "#ASSERT%a %a : %a.@." bool b term t term u
  | P_assert_conv(t,u) -> out ppf "#ASSERT%a %a == %a.@." bool b term t term u

let strat : Eval.strat pp = fun ppf {strategy; steps} ->
  match strategy, steps with
  | NONE, _
  | HNF, _ -> assert false
  | WHNF, None -> out ppf "[WHNF]"
  | WHNF, Some k -> out ppf "[%d,WHNF]" k
  | SNF, None -> ()
  | SNF, Some k -> out ppf "[%d]" k

let query : p_query pp = fun ppf ({elt;pos} as q) ->
  match elt with
  | P_query_verbose _
  | P_query_debug _
  | P_query_prover _
  | P_query_prover_timeout _
  | P_query_print _
  | P_query_proofterm
  | P_query_search _
  | P_query_flag _ -> out ppf "(;%a;)" Pretty.query q (*FIXME?*)
  | P_query_infer(_,{strategy=(SNF|HNF|WHNF);_})
  | P_query_normalize(_,{strategy=(NONE|HNF);_}) ->
      fatal pos "Cannot be translated: %a" Pretty.query q
  | P_query_assert(b,a) -> assertion ppf (b,a)
  | P_query_infer(t,{strategy=NONE;_}) -> out ppf "#INFER %a.@." term t
  | P_query_normalize(t,s) -> out ppf "#EVAL%a %a.@." strat s term t

let modifier : bool -> p_modifier pp = fun ac ppf ({elt;pos} as m) ->
  match elt with
  | P_mstrat Eager
  | P_expo Public
  | P_prop Const -> ()
  | P_expo Protec -> out ppf "private "
  | P_prop Defin -> if ac then out ppf "defac " else out ppf "def "
  | P_prop Injec -> out ppf "injective "
  | P_opaq -> out ppf "thm "
  | P_expo Privat -> out ppf "(;private;) " (*FIXME?*)
  | P_mstrat Sequen ->
      fatal pos "Cannot be translated: %a@." Pretty.modifier m
  | P_prop (AC _) -> assert false
  | P_prop Commu -> assert false
  | P_prop (Assoc _) -> assert false

let a_or_c {elt;_} =
  match elt with
  | P_prop (AC _) -> assert false
  | P_prop Commu | P_prop (Assoc _) -> true
  | _ -> false

let is_ac ms =
  match ms with
  | [] -> false
  | [{elt=P_prop Commu;_}; {elt=P_prop(Assoc _);_}]
  | [{elt=P_prop(Assoc _);_}; {elt=P_prop Commu;_}] -> true
  | [{elt=P_prop Commu;pos} as m]
  | [{elt=P_prop(Assoc _);pos} as m] ->
      fatal pos "Cannot be translated: %a@." Pretty.modifier m
  | {pos;_}::_ -> fatal pos "Modifier repetition."

let rule : p_rule pp =
  let varset ppf set = List.pp string " " ppf (StrSet.elements set) in
  fun ppf {elt=(l,r);_} ->
  out ppf "[%a] %a --> %a.@." varset (pvars_lhs l) term l term r

let command : p_command pp = fun ppf ({elt; pos} as c) ->
  match elt with
  | P_query q -> query ppf q
  | P_require(false,ps) -> out ppf "#REQUIRE %a.@." (List.pp path " ") ps
  | P_symbol{p_sym_mod; p_sym_nam=n; p_sym_arg=xs; p_sym_typ;
             p_sym_trm; p_sym_prf=None; p_sym_def=_;} ->
      let typ ppf = out ppf " : %a%a" prod xs term in
      let dfn ppf = out ppf " := %a%a" abs xs term in
      let ac, ms = List.partition a_or_c p_sym_mod in
      out ppf "%a%a%a%a.@." (List.pp (modifier (is_ac ac)) "") ms ident n
        (Option.pp typ) p_sym_typ (Option.pp dfn) p_sym_trm
  | P_rules rs -> List.iter (rule ppf) rs
  | P_builtin _
  | P_unif_rule _
  | P_coercion _
    -> () (*FIXME?*)
  | P_inductive _
  | P_open _
  | P_require_as _
  | P_notation _
  | P_opaque _
  | P_require(true,_)
  | P_symbol{p_sym_prf=Some _; _}
    -> fatal pos "Cannot be translated: %a" Pretty.command c

let ast : ast pp = fun ppf -> Stream.iter (command ppf)

let print : ast -> unit = ast std_formatter
