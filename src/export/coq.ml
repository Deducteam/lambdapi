(** Translate the parser-level AST to Coq. *)

open Lplib open Base
open Common open Pos open Error
open Parsing open Syntax
open Format
open Core open Term

let log = Logger.make 'x' "xprt" "export"
let log = log.pp

let stt = Stdlib.ref true

type config =
  { sym_Set : qident
  ; sym_prop : qident (* : Set *)
  ; sym_arr : qident (* : Set → Set → Set *)
  ; sym_El : qident (* : Set → TYPE *)
  ; sym_imp : qident (* El prop → El prop → El prop *)
  ; sym_all : qident (* Π [a : Set], (El a → El prop) → El prop *)
  ; sym_Prf : qident (* El prop → TYPE *) }

let default_config =
  let path = ["STTfa"] in
  { sym_Set = path, "Set"
  ; sym_prop = path, "prop"
  ; sym_arr = path, "arr"
  ; sym_El = path, "El"
  ; sym_imp = path, "imp"
  ; sym_all = path, "all"
  ; sym_Prf = path, "Prf" }

let get_config : string -> config = fun f ->
  let sym_Set = ref None and sym_prop = ref None and sym_arr = ref None
  and sym_El = ref None and sym_imp = ref None and sym_all = ref None
  and sym_Prf = ref None in
  let consume = function
    | {elt=P_builtin("Set",{elt;_});_} -> sym_Set := Some elt
    | {elt=P_builtin("prop",{elt;_});_} -> sym_prop := Some elt
    | {elt=P_builtin("arr",{elt;_});_} -> sym_arr := Some elt
    | {elt=P_builtin("El",{elt;_});_} -> sym_El := Some elt
    | {elt=P_builtin("imp",{elt;_});_} -> sym_imp := Some elt
    | {elt=P_builtin("all",{elt;_});_} -> sym_all := Some elt
    | {elt=P_builtin("Prf",{elt;_});_} -> sym_Prf := Some elt
    | {pos;_} -> fatal pos "Invalid command."
  in
  Stream.iter consume (Parser.parse_file f);
  let get n = function
    | Some x -> x
    | None ->
        let pos =
          Some {fname=Some f;start_line=0;start_col=0;end_line=0;end_col=0} in
        fatal pos "Builtin %s undefined." n
  in
  { sym_Set = get "Set" !sym_Set;
    sym_prop = get "prop" !sym_prop;
    sym_arr = get "arr" !sym_arr;
    sym_El = get "El" !sym_El;
    sym_imp = get "imp" !sym_imp;
    sym_all = get "all" !sym_all;
    sym_Prf = get "Prf" !sym_Prf }

let translate_ident : string -> string =
  let re = Str.regexp "[():\\<>^]" in
  fun s ->
    match s with
    (* Coq keywords
       https://coq.inria.fr/distrib/current/refman/language/core/basic.html *)
    | "_" | "Axiom" | "CoFixpoint" | "Definition" | "Fixpoint" | "Hypothesis"
    | "Parameter" | "Prop" | "SProp" | "Set" | "Theorem" | "Type" | "Variable"
    | "as" | "at" | "cofix" | "else" | "end" | "fix" | "for" | "forall"
    | "fun" | "if" | "in" | "let" | "match" | "return" | "then" | "where"
    | "with" | "by" | "exists" | "exists2" | "using" -> "_" ^ s
    | _ ->
      let s = Str.global_replace re "_" (Escape.unescape s) in
      if s <> "" && s.[0] = '\'' then "_" ^ s else s

let raw_ident : string pp = fun ppf s -> Print.uid ppf (translate_ident s)

let ident : p_ident pp = fun ppf {elt;_} -> raw_ident ppf elt

let meta_ident : p_meta_ident pp = fun ppf {elt;_} -> out ppf "%d" elt

let param_id : p_ident option pp = fun ppf idopt ->
  match idopt with
  | Some(id) -> out ppf "%a" ident id
  | None     -> out ppf "_"

let param_ids : p_ident option list pp = List.pp param_id " "

let raw_path : Path.t pp = List.pp raw_ident "."

let path : p_path pp = fun ppf {elt;_} -> raw_path ppf elt

let qident : p_qident pp = fun ppf {elt=(mp,s);_} ->
  match mp with
  | [] -> raw_ident ppf s
  | _::_ -> out ppf "%a.%a" raw_path mp raw_ident s

(* ends with a space *)
let modifier : p_modifier pp = fun ppf {elt; _} ->
  match elt with
  | P_expo(e)   -> Print.expo ppf e
  | P_mstrat(s) -> Print.match_strat ppf s
  | P_prop(p)   -> Print.prop ppf p
  | P_opaq      -> out ppf "opaque "

(* ends with a space if the list is not empty *)
let modifiers : p_modifier list pp = List.pp modifier ""

(** The possible priority levels are [`Func] (top level, including abstraction
   and product), [`Appl] (application) and [`Atom] (smallest priority). *)
type priority = [`Func | `Appl | `Atom]

let cfg = Stdlib.ref default_config

let rec term : p_term pp = fun ppf t ->
  let empty_context = ref true in
  let rec atom ppf t = pp `Atom ppf t
  and appl ppf t = pp `Appl ppf t
  and func ppf t = pp `Func ppf t
  and pp priority ppf t =
    if Logger.log_enabled() then log "%a: %a" Pos.short t.pos Pretty.term t;
    match (t.elt, priority) with
    | P_Type, _ -> out ppf "Type"
    | P_Iden({elt;_},_), _
      when !stt && elt = !cfg.sym_Set -> out ppf "Type"
    | P_Iden({elt;_},_), _
      when !stt && elt = !cfg.sym_prop -> out ppf "Prop"
    | P_Iden(qid,false), _ -> out ppf "%a" qident qid
    | P_Iden(qid,true), _ -> out ppf "@@%a" qident qid
    | P_Wild, _ -> out ppf "_"
    | P_Meta(mid,_), _ -> out ppf "TODO(*?%a*)" meta_ident mid
    | P_Patt(idopt,ts), _ -> out ppf "%a%a" param_id idopt env ts
    | P_Arro(a,b), `Func -> out ppf "@[%a@ -> %a@]" appl a func b
    | P_Abst(xs,t), `Func ->
        let fn (ids,_,_) = List.for_all ((=) None) ids in
        let ec = !empty_context in
        empty_context := ec && List.for_all fn xs;
        out ppf "@[<2>fun%a =>@ %a@]"
          params_list xs
          func t;
        empty_context := ec
    | P_Prod(xs,b), `Func ->
        out ppf "@[<2>forall%a,@ %a@]" params_list xs func b
    | P_LLet(x,xs,a,t,u), `Func ->
        out ppf "@[@[<hv2>let @[<2>%a%a%a@] :=@ %a@ @]in@ %a@]"
          ident x params_list xs typ a func t func u
    | P_NLit i, _ -> out ppf "TODO(*%s*)" i
    | P_Wrap t, _ -> pp priority ppf t
    | P_Expl t, _ -> out ppf "TODO(*{@[<hv2>%a@]}*)" func t
    | P_Appl(a,b), _ ->
      begin
        match p_get_args t with
        | {elt=P_Iden({elt;_},_);_}, [u]
             when !stt && (elt = !cfg.sym_El || elt = !cfg.sym_Prf) ->
            pp priority ppf u
        (* The cases below are not necessary: they just unfold the definitions
           of arr, imp and all in STTfa.v. *)
        | {elt=P_Iden({elt;_},_);_}, [u1;u2]
             when !stt && (elt = !cfg.sym_arr || elt = !cfg.sym_imp) ->
            pp priority ppf {t with elt=P_Arro(u1,u2)}
        | {elt=P_Iden({elt;_},_);_},[_;{elt=P_Abst([_] as xs,u2);_}]
             when !stt && elt = !cfg.sym_all ->
          pp priority ppf {t with elt=P_Prod(xs,u2)}
        | _ -> application priority ppf t a b
      end
    | _ -> out ppf "(@[<hv2>%a@])" func t
  and application priority ppf t a b =
    match priority with
    | `Appl | `Func -> out ppf "@[%a@ %a@]" appl a atom b
    | _ -> out ppf "(@[<hv2>%a@])" func t
  and env ppf ts =
    match ts with
    | None -> ()
    | Some [||] when !empty_context -> ()
    | Some ts -> out ppf "[%a]" (Array.pp func "; ") ts
  in
  let rec toplevel ppf t =
    match t.elt with
    | P_Abst(xs,t) -> out ppf "@[<2>fun%a =>@ %a@]" params_list xs toplevel t
    | P_Prod(xs,b) -> out ppf "@[<2>forall%a,@ %a@]" params_list xs toplevel b
    | P_Arro(a,b) -> out ppf "@[%a@ -> %a@]" appl a toplevel b
    | P_LLet(x,xs,a,t,u) ->
        out ppf "@[@[<hv2>let @[<2>%a%a%a@] :=@ %a@ @]in@ %a@]"
          ident x params_list xs typ a toplevel t toplevel u
    | _ -> func ppf t
  in
  toplevel ppf t

and params : p_params pp = fun ppf (ids, t, b) ->
  match t with
  | Some t ->
    begin match b with
    | false -> out ppf "@[(@,@[<2>%a@ : %a@]@,)@]" param_ids ids term t
    | true  -> out ppf "@[{@,@[<2>%a@ : %a@]@,}@]" param_ids ids term t
    end
  | None -> param_ids ppf ids

(* starts with a space if the list is not empty *)
and params_list : p_params list pp = fun ppf ->
  List.iter (out ppf "@ %a" params)

(* starts with a space if <> None *)
and typ : p_term option pp = fun ppf t ->
  Option.iter (out ppf "@ : %a" term) t

let rule : string -> p_rule pp = fun kw ppf {elt=(l,r);_} ->
  out ppf "(*%s %a ↪ %a*)" kw term l term r

let inductive : string -> p_inductive pp =
  let cons ppf (id,a) = out ppf "| %a : %a" ident id term a in
  fun kw ppf {elt=(id,a,cs);_} ->
  out ppf "@[<v>%s %a : %a :=@,%a@]" kw ident id term a (List.pp cons "@,") cs

let proof_end : p_proof_end pp = fun ppf pe ->
  out ppf (match pe.elt with
           | P_proof_end   -> "Qed"
           | P_proof_admitted -> "Admitted"
           | P_proof_abort -> "Abort")

let rw_patt : p_rw_patt pp = fun ppf p ->
  match p.elt with
  | Rw_Term(t)               -> term ppf t
  | Rw_InTerm(t)             -> out ppf "in %a" term t
  | Rw_InIdInTerm(x,t)       -> out ppf "in %a in %a" ident x term t
  | Rw_IdInTerm(x,t)         -> out ppf "%a in %a" ident x term t
  | Rw_TermInIdInTerm(u,(x,t)) ->
      out ppf "%a in %a in %a" term u ident x term t
  | Rw_TermAsIdInTerm(u,(x,t)) ->
      out ppf "%a as %a in %a" term u ident x term t

let tactic : p_tactic pp = fun ppf { elt;  _ } ->
  begin match elt with
  | P_tac_admit -> out ppf "admit"
  | P_tac_apply t -> out ppf "apply %a" term t
  | P_tac_assume ids ->
      out ppf "assume%a" (List.pp (unit " " |+ param_id) "") ids
  | P_tac_fail -> out ppf "fail"
  | P_tac_generalize id -> out ppf "generalize %a" ident id
  | P_tac_have (id, t) -> out ppf "have %a: %a" ident id term t
  | P_tac_induction -> out ppf "induction"
  | P_tac_query _ -> ()
  | P_tac_refine t -> out ppf "refine %a" term t
  | P_tac_refl -> out ppf "reflexivity"
  | P_tac_rewrite(b,p,t)     ->
      let dir ppf b = if not b then out ppf " left" in
      let pat ppf p = out ppf " [%a]" rw_patt p in
      out ppf "rewrite%a%a %a" dir b (Option.pp pat) p term t
  | P_tac_simpl None -> out ppf "simpl"
  | P_tac_simpl (Some qid) -> out ppf "simpl %a" qident qid
  | P_tac_solve -> out ppf "solve"
  | P_tac_sym -> out ppf "symmetry"
  | P_tac_why3 p ->
      let prover ppf s = out ppf " %S" s in
      out ppf "why3%a" (Option.pp prover) p
  end;
  out ppf ";"

(* starts with a space if distinct from [Pratter.Neither] *)
let assoc : Pratter.associativity pp = fun ppf a ->
  out ppf (match a with
           | Pratter.Neither -> ""
           | Pratter.Left -> " left"
           | Pratter.Right -> " right")

let notation : string Sign.notation pp = fun ppf -> function
  | Infix (a, p) -> out ppf "infix%a %s" assoc a p
  | Prefix p -> out ppf "prefix %s" p
  | Quant -> out ppf "quantifier"
  | _ -> ()

let rec subproof : p_subproof pp = fun ppf sp ->
  out ppf "{@[<hv2>@ %a@ @]}" proofsteps sp

and subproofs : p_subproof list pp = fun ppf spl ->
  out ppf "@[<hv>%a@]" (pp_print_list ~pp_sep:pp_print_space subproof) spl

and proofsteps : p_proofstep list pp = fun ppf psl ->
  pp_print_list ~pp_sep:pp_print_space proofstep ppf psl

and proofstep : p_proofstep pp = fun ppf (Tactic (t, spl)) ->
  out ppf "@[<hv2>%a@,%a;@]" tactic t subproofs spl

let proof : (p_proof * p_proof_end) pp = fun ppf (prf, prf_end) ->
  out ppf "Proof.@ @[<2>%a@]@ %a"
    (List.pp subproof "@ ") prf
    proof_end prf_end

let command : p_command pp = fun ppf { elt; _ } ->
  begin match elt with
  | P_coercion _ -> ()
  | P_builtin _ -> ()
  | P_inductive (_, _, []) -> assert false (* not possible *)
  | P_inductive (ms, xs, i :: il) ->
      out ppf "@[<v>@[%a%a@]%a@,%a@,end@]"
        modifiers ms
        (List.pp params " ") xs
        (inductive "Inductive") i
        (List.pp (inductive "and") "@,") il
  | P_notation (qid, n) ->
    out ppf "(*Notation %a %a.*)@." qident qid notation n
  | P_open ps -> out ppf "Import %a@." (List.pp path " ") ps
  | P_query _ -> ()
  | P_require (b, ps) ->
      out ppf "Require%a %a.@."
        (pp_if b (unit " Import")) ()
        (List.pp path " ") ps
  | P_require_as (p,i) -> out ppf "@[Module %a@ := %a@].@." ident i path p
  | P_rules [] -> assert false (* not possible *)
  | P_rules (r::rs) ->
    out ppf "@[<v>%a@,%a@]" (rule "rule") r (List.pp (rule "with") "@,") rs
  | P_symbol
    { p_sym_mod=_; p_sym_nam; p_sym_arg; p_sym_typ;
      p_sym_trm; p_sym_prf; p_sym_def } ->
    begin
      out ppf "@[<v>@[<2>%s %a%a%a%a%a.@]%a@]@."
        (if p_sym_def then "Definition" else "Axiom")
        ident p_sym_nam
        params_list p_sym_arg
        typ p_sym_typ
        (pp_if p_sym_def (unit "@ :=")) ()
        (Option.pp (sep " " |+ term)) p_sym_trm
        (Option.pp (unit "@," |+ proof)) p_sym_prf
    end
  | P_unif_rule _ -> ()
  end

let ast : ast pp = fun ppf -> Stream.iter (command ppf)

(** [print b ast] sets [stt] to [b] and translates [ast] to Coq on standard
    output. *)
let print : config option -> ast -> unit = fun c a ->
  begin match c with
  | None -> stt := false
  | Some c -> stt := true; cfg := c
  end; ast std_formatter a
