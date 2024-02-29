(** Translate the parser-level AST to Dedukti. *)

open Lplib open Base open Extra
open Common open Pos open Error
open Parsing open Syntax
open Format
open Core open Eval open Term

let raw_ident : string pp = fun ppf s -> Dk.ident ppf s

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
  | P_Arro(u,v) -> out ppf "%a -> %a" pterm u term v
  | P_Abst(xs,u) -> out ppf "%a%a" abs xs term u
  | P_Prod(xs,u) -> out ppf "%a%a" prod xs term u
  | P_LLet(x,xs,a,u,v) ->
      out ppf "(%a%a => %a) %a"
        ident x (Option.pp (let_typ xs)) a term v (let_dfn xs) u
  | P_Wrap u -> out ppf "(%a)" term u
  | P_Appl(u,v) -> out ppf "%a %a" term u pterm v

and let_typ : p_params list -> p_term pp = fun xs ppf u ->
  match xs with
  | [] -> typ ppf u
  | _ -> out ppf ": (%a%a)" prod xs term u

and let_dfn : p_params list -> p_term pp = fun xs ppf u ->
  match xs with
  | [] -> pterm ppf u
  | _ -> out ppf "(%a%a)" abs xs term u

and pterm : p_term pp = fun ppf t ->
  match t.elt with
  (* doesn't need surrounding parentheses *)
  | P_Meta _
  | P_Patt(_,None)
  | P_Expl _
  | P_Type
  | P_Wild
  | P_NLit _
  | P_Iden _
  | P_Wrap _
    -> term ppf t
  (* add surrounding parentheses *)
  | P_Patt(_,Some _)
  | P_Arro _
  | P_Abst _
  | P_Prod _
  | P_LLet _
  | P_Appl _
    -> out ppf "(%a)" term t

and terms : p_term array pp = fun ppf -> Array.iter (out ppf " %a" term)

and param : p_term option -> string -> p_ident option pp = fun a sep ppf id ->
  if sep = "" then
    match a with
    | None -> out ppf " %a" param_id id
    | Some a -> out ppf " (%a%a)" param_id id typ a
  else out ppf "%a%a%s" param_id id (Option.pp typ) a sep

and params : string -> p_params pp = fun sep ppf (ids,a,_) ->
  match ids, a with
  | None::_, None ->
      fatal_no_pos "Cannot translate \"_\" parameters with no type."
  | Some {pos;_}::_, None ->
      fatal pos "Cannot translate parameters with no type."
  | _ -> List.iter (out ppf "%a" (param a sep)) ids

and params_list : string -> p_params list pp = fun sep ppf ->
  List.iter (out ppf "%a" (params sep))

and abs : p_params list pp = fun ppf -> params_list " => " ppf
and prod : p_params list pp = fun ppf -> params_list " -> " ppf
and arg : p_params list pp = fun ppf -> params_list "" ppf

and typ : p_term pp = fun ppf t -> out ppf " : %a" pterm t

let bool : bool pp = fun ppf b -> if not b then out ppf "NOT"

let assertion : (bool * p_assertion) pp = fun ppf (b,a) ->
  match a with
  | P_assert_typing(t,u) ->
      out ppf "#ASSERT%a %a : %a.@." bool b term t term u
  | P_assert_conv(t,u) ->
      out ppf "#ASSERT%a %a == %a.@." bool b pterm t pterm u

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
  | P_query_assert(b,a) -> assertion ppf (not b,a)
  | P_query_infer(t,{strategy=NONE;_}) -> out ppf "#INFER %a.@." term t
  | P_query_normalize(t,s) -> out ppf "#EVAL%a %a.@." strat s term t

(*https://github.com/Deducteam/Dedukti/issues/318*)
let rec remove_wraps ({elt;_} as t) =
  match elt with
  | P_Wrap u -> remove_wraps u
  | _ -> t

let rule : p_rule pp =
  let varset ppf set = List.pp string ", " ppf (StrSet.elements set) in
  fun ppf {elt=(l,r);_} ->
  out ppf "[%a] %a --> %a.@." varset (pvars_lhs l) term (remove_wraps l) term r

let partition_modifiers ms =
  let ms = List.map (fun {elt;_} -> elt) ms in
  let ms = List.sort_uniq Stdlib.compare ms in
  let is_prop elt = match elt with P_prop _ -> true | _ -> false in
  let props, non_props = List.partition is_prop ms in
  let props = List.map (function P_prop p -> p | _ -> assert false) props in
  let is_expo elt = match elt with P_expo _ -> true | _ -> false in
  let expos, non_expos = List.partition is_expo non_props in
  let expos = List.map (function P_expo e -> e | _ -> assert false) expos in
  let is_mstrat elt = match elt with P_mstrat _ -> true | _ -> false in
  let mstrats, opaqs = List.partition is_mstrat non_expos in
  let mstrats =
    List.map (function P_mstrat s -> s | _ -> assert false) mstrats in
  (* we ignore private symbols *)
  let expos = List.filter (function Privat -> false | _ -> true) expos in
  props, expos, mstrats, opaqs

(* check Stdlib.compare on modifiers. *)
let _ =
  assert (Stdlib.compare Commu (Assoc true) < 0)
  ;assert (Stdlib.compare Commu (Assoc false) < 0)

(* translation of lists of modifiers:
- [opaque] --> "thm"
- [protected?; associative; commutative] --> "private"? "defac"
- [protected?; injective] --> "private"? "injective"
- [protected] --> "private"
- [constant] --> ""
- [] --> "def" *)
let modifiers : p_term option -> p_modifier list pp = fun p_sym_typ ppf ms ->
  match partition_modifiers ms with
  | [], [], [], [] -> out ppf "def "
  | [], [], [], [P_opaq] when p_sym_typ <> None -> out ppf "thm "
  (*https://github.com/Deducteam/Dedukti/issues/319*)
  | [Commu;Assoc _], [Protec], [], [] -> out ppf "defac "
  | [Injec], [Protec], [], [] -> out ppf "private injective "
  | [Injec], [], [], [] -> out ppf "injective "
  | [], [Protec], [], [] -> out ppf "private "
  | [Const], [], [], [] -> ()
  | _ ->
      match ms with
      | [] -> assert false
      | {pos;_}::_ -> fatal pos "Cannot translate: %a.@." Pretty.modifiers ms

let command : p_command pp = fun ppf ({elt; pos} as c) ->
  match elt with
  | P_query q -> query ppf q
  | P_require(false,ps) ->
      List.iter (fun {elt;_} -> out ppf "#REQUIRE %a@." Dk.path elt) ps
  | P_symbol{p_sym_mod; p_sym_nam=n; p_sym_arg=xs; p_sym_typ;
             p_sym_trm; p_sym_prf=None; p_sym_def=_;} ->
      begin match p_sym_trm, p_sym_typ with
      | Some t, _ ->
          let dfn ppf = out ppf " := %a" term in
          out ppf "%a%a%a%a%a.@." (modifiers p_sym_typ) p_sym_mod ident n
            arg xs (Option.pp typ) p_sym_typ dfn t
      | None, Some a ->
          (*https://github.com/Deducteam/Dedukti/issues/322*)
          out ppf "%a%a : %a%a.@." (modifiers p_sym_typ) p_sym_mod ident n
            prod xs term a
      | _ -> assert false
      end
  | P_rules rs -> List.iter (rule ppf) rs
  | P_builtin _
  | P_unif_rule _
  | P_coercion _
    -> () (*FIXME?*)
  | P_inductive _
  | P_open _
  | P_require_as _
  | P_notation _ (* FIXME: accept quantifier notations *)
  | P_opaque _
  | P_require(true,_)
  | P_symbol{p_sym_prf=Some _; _}
    -> fatal pos "Cannot be translated: %a" Pretty.command c

let ast : ast pp = fun ppf -> Stream.iter (command ppf)

let print : ast -> unit = ast std_formatter
