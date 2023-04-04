(** Translate the parser-level AST to Coq.

There are two modes:

- raw_coq mode (option -o raw_coq): translation of the AST as it is
  (lambdapi-calculus is a subset system of coq if we ignore rules)

- stt_coq mode (option -o stt_coq): translation of the AST as an encoding in
  simple type theory.

  The encoding can be specified through a lambdapi file (option --encoding).

In both modes, a renaming map can be provided to rename some identifiers.

The renaming map can be specified through a lambdapi file (option --renaming).
*)

open Lplib open Base open Extra
open Common open Pos open Error
open Parsing open Syntax
open Format
open Core

let log = Logger.make 'x' "xprt" "export"
let log = log.pp

(** Symbols necessary to encode STT. *)

let path = ["STTfa"]

let sym_Set = Stdlib.ref (path,"Set") (* : TYPE *)
let sym_prop = Stdlib.ref (path,"prop") (* : Set *)
let sym_arr = Stdlib.ref (path,"arr") (* : Set → Set → Set *)
let sym_El = Stdlib.ref (path,"El") (* : Set → TYPE *)
let sym_imp = Stdlib.ref (path,"imp") (* El prop → El prop → El prop *)
let sym_all = Stdlib.ref (path,"all")
  (* Π [a : Set], (El a → El prop) → El prop *)
let sym_Prf = Stdlib.ref (path,"Prf") (* El prop → TYPE *)

let sym_Set_name = Stdlib.ref (snd !sym_Set)
let sym_prop_name = Stdlib.ref (snd !sym_prop)
let sym_arr_name = Stdlib.ref (snd !sym_arr)
let sym_El_name = Stdlib.ref (snd !sym_El)
let sym_imp_name = Stdlib.ref (snd !sym_imp)
let sym_all_name = Stdlib.ref (snd !sym_all)
let sym_Prf_name = Stdlib.ref (snd !sym_Prf)

type code = Arr | Imp | All | Set | Other

let sym_map = Stdlib.ref StrMap.empty

let update_sym_map() =
  sym_map :=
    StrMap.add !sym_arr_name Arr
      (StrMap.add !sym_imp_name Imp
         (StrMap.add !sym_all_name All
            (StrMap.add !sym_Set_name Set
               (StrMap.add !sym_prop_name Set
                  (StrMap.add !sym_El_name Set
                     (StrMap.add !sym_Prf_name Set
                        StrMap.empty))))))

let _ = update_sym_map()

let code n = try StrMap.find n !sym_map with Not_found -> Other

let set_encoding : string -> unit = fun f ->
  let opt_sym_Set = ref None and opt_sym_prop = ref None
  and opt_sym_arr = ref None and opt_sym_El = ref None
  and opt_sym_imp = ref None and opt_sym_all = ref None
  and opt_sym_Prf = ref None in
  let consume = function
    | {elt=P_builtin("Set",{elt;_});_} -> opt_sym_Set := Some elt
    | {elt=P_builtin("prop",{elt;_});_} -> opt_sym_prop := Some elt
    | {elt=P_builtin("arr",{elt;_});_} -> opt_sym_arr := Some elt
    | {elt=P_builtin("El",{elt;_});_} -> opt_sym_El := Some elt
    | {elt=P_builtin("imp",{elt;_});_} -> opt_sym_imp := Some elt
    | {elt=P_builtin("all",{elt;_});_} -> opt_sym_all := Some elt
    | {elt=P_builtin("Prf",{elt;_});_} -> opt_sym_Prf := Some elt
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
  sym_Set := get "Set" !opt_sym_Set; sym_Set_name := snd !sym_Set;
  sym_prop := get "prop" !opt_sym_prop; sym_prop_name := snd !sym_prop;
  sym_arr := get "arr" !opt_sym_arr; sym_arr_name := snd !sym_arr;
  sym_El := get "El" !opt_sym_El; sym_El_name := snd !sym_El;
  sym_imp := get "imp" !opt_sym_imp; sym_imp_name := snd !sym_imp;
  sym_all := get "all" !opt_sym_all; sym_all_name := snd !sym_all;
  sym_Prf := get "Prf" !opt_sym_Prf; sym_Prf_name := snd !sym_Prf;
  update_sym_map()
;;

(* Get a renaming map from a file. *)

let rmap = ref StrMap.empty

let set_renaming : string -> unit = fun f ->
  let consume = function
    | {elt=P_builtin(n,{elt=(p,s);_});_} ->
        let v = if p = [] then s else String.concat "." p ^ "." ^ s in
        rmap := StrMap.add n v !rmap
    | {pos;_} -> fatal pos "Invalid command."
  in
  Stream.iter consume (Parser.parse_file f)

(* Translation. *)

let translate_ident : string -> string = fun s ->
  try StrMap.find s !rmap with Not_found -> s

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

let stt = Stdlib.ref false

let rec term : p_term pp = fun ppf t ->
  let empty_context = ref true in
  let rec atom ppf t = pp `Atom ppf t
  and appl ppf t = pp `Appl ppf t
  and func ppf t = pp `Func ppf t
  and pp priority ppf t =
    if Logger.log_enabled() then log "%a: %a" Pos.short t.pos Pretty.term t;
    match t.elt, priority with
    | P_Type, _ -> out ppf "Type"
    | P_Iden({elt;_},_), _
      when !stt && elt = !sym_Set -> out ppf "Type"
    | P_Iden({elt;_},_), _
      when !stt && elt = !sym_prop -> out ppf "Prop"
    | P_Iden(qid,true), _ -> out ppf "@@%a" qident qid
    | P_Iden(qid,false), _ -> qident ppf qid
    | P_NLit i, _ -> raw_ident ppf i
    | P_Wild, _ -> out ppf "_"
    | P_Meta(mid,_), _ -> out ppf "TODO(*?%a*)" meta_ident mid
    | P_Patt _, _ -> assert false
    | P_Arro(a,b), `Func -> out ppf "%a -> %a" appl a func b
    | P_Abst(xs,t), `Func ->
        let fn (ids,_,_) = List.for_all ((=) None) ids in
        let ec = !empty_context in
        empty_context := ec && List.for_all fn xs;
        out ppf "fun%a => %a" params_list xs func t;
        empty_context := ec
    | P_Prod(xs,b), `Func ->
        out ppf "forall%a, %a" params_list xs func b
    | P_LLet(x,xs,a,t,u), `Func ->
        out ppf "let %a%a%a := %a in %a"
          ident x params_list xs typopt a func t func u
    | P_Expl t, _ -> out ppf "TODO(*{%a}*)" func t
    | P_Appl(a,b), _ ->
      begin
        match p_get_args t with
        | {elt=P_Iden({elt;_},_);_}, [u]
             when !stt && (elt = !sym_El || elt = !sym_Prf) ->
            pp priority ppf u
        (* The cases below are not necessary: they just unfold the definitions
           of arr, imp and all in STTfa.v. *)
        | {elt=P_Iden({elt;_},_);_}, [u1;u2]
             when !stt && (elt = !sym_arr || elt = !sym_imp) ->
            pp priority ppf {t with elt=P_Arro(u1,u2)}
        | {elt=P_Iden({elt;_},_);_},[_;{elt=P_Abst([_] as xs,u2);_}]
             when !stt && elt = !sym_all ->
          pp priority ppf {t with elt=P_Prod(xs,u2)}
        | _ -> application priority ppf t a b
      end
    | P_Wrap t, _ -> out ppf "(%a)" func t
    | _ -> out ppf "(%a)" func t
  and application priority ppf t a b =
    match priority with
    | `Appl | `Func -> out ppf "%a %a" appl a atom b
    | _ -> out ppf "(%a)" func t
  in
  let rec toplevel ppf t =
    match t.elt with
    | P_Abst(xs,t) -> out ppf "fun%a => %a" params_list xs toplevel t
    | P_Prod(xs,b) -> out ppf "forall%a, %a" params_list xs toplevel b
    | P_Arro(a,b) -> out ppf "%a -> %a" appl a toplevel b
    | P_LLet(x,xs,a,t,u) ->
        out ppf "let %a%a%a := %a in %a"
          ident x params_list xs typopt a toplevel t toplevel u
    | _ -> func ppf t
  in
  toplevel ppf t

and params : p_params pp = fun ppf (ids, t, b) ->
  match b, t with
  | true, Some t -> out ppf "{%a : %a}" param_ids ids term t
  | false, Some t -> out ppf "(%a : %a)" param_ids ids term t
  | true, None -> out ppf "{%a}" param_ids ids
  | false, None -> param_ids ppf ids

(* starts with a space if the list is not empty *)
and params_list : p_params list pp = fun ppf ->
  List.iter (out ppf " %a" params)

(* starts with a space if <> None *)
and typopt : p_term option pp = fun ppf t ->
  Option.iter (out ppf " : %a" term) t

let inductive : string -> p_inductive pp =
  let cons ppf (id,a) = out ppf "| %a : %a" ident id term a in
  fun kw ppf {elt=(id,a,cs);_} ->
  out ppf "@[<v>%s %a : %a :=@,%a@]" kw ident id term a (List.pp cons "@,") cs

let command : p_command pp = fun ppf ({ elt; _ } as cmd) ->
  begin match elt with
  | P_inductive (_, _, []) -> assert false
  | P_inductive (ms, xs, i :: il) ->
      out ppf "@[<v>@[%a%a@]%a@,%a@,end@]"
        modifiers ms
        (List.pp params " ") xs
        (inductive "Inductive") i
        (List.pp (inductive "and") "@,") il
  | P_open ps -> out ppf "Import %a" (List.pp path " ") ps
  | P_require (true, ps) ->
      out ppf "Require Import %a." (List.pp path " ") ps
  | P_require (false, ps) ->
      out ppf "Require %a." (List.pp path " ") ps
  | P_require_as (p,i) -> out ppf "Module %a := %a." ident i path p
  | P_symbol
    { p_sym_mod; p_sym_nam; p_sym_arg; p_sym_typ;
      p_sym_trm; p_sym_prf=_; p_sym_def } ->
      begin match code p_sym_nam.elt with
      | Set -> ()
      | Imp -> out ppf "Definition imp (P Q: Prop) := P -> Q."
      | Arr -> out ppf "Definition arr (A:Type) (B:Type) := A -> B."
      | All ->
          out ppf "Definition all (A:Type) (P:A->Prop) := forall x:A, P x."
      | Other ->
          match p_sym_def, p_sym_trm, p_sym_arg, p_sym_typ with
          | true, Some t, _, _ ->
              if List.exists is_opaq p_sym_mod then
                out ppf "Lemma %a%a%a. Proof. exact (%a). Qed."
                  ident p_sym_nam params_list p_sym_arg typopt p_sym_typ
                  term t
              else
                out ppf "Definition %a%a%a := %a."
                  ident p_sym_nam params_list p_sym_arg typopt p_sym_typ
                  term t
          | false, _, [], Some t ->
              out ppf "Axiom %a : %a." ident p_sym_nam term t
          | false, _, _, Some t ->
              out ppf "Axiom %a : forall%a, %a."
                ident p_sym_nam params_list p_sym_arg term t
          | _ -> assert false
      end
  | _ -> out ppf "(*%a*)" Pretty.command cmd
  end

let command ppf = out ppf "%a@." command

let ast : ast pp = fun ppf -> Stream.iter (command ppf)

let print : ast -> unit = ast std_formatter
