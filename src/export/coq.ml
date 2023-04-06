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

type builtin =
  Set | Prop | Arr | El | Imp | All | Prf | Eq | Or | And | Ex | Not

let index_of_builtin = function
  | Set -> 0 | Prop -> 1 | Arr -> 2 | El -> 3 | Imp -> 4 | All -> 5
  | Prf -> 6 | Eq -> 7 | Or -> 8 | And -> 9 | Ex -> 10 | Not -> 11

let nb_builtins = 12

let builtin_of_index = function
  | 0 -> Set | 1 -> Prop | 2 -> Arr | 3 -> El | 4 -> Imp | 5 -> All
  | 6 -> Prf | 7 -> Eq | 8 -> Or | 9 -> And | 10 -> Ex | 11 -> Not
  | _ -> assert false

let _ = (* sanity check *)
  for i = 0 to nb_builtins - 1 do
    assert (index_of_builtin (builtin_of_index i) = i)
  done

let index_of_name = function
  | "Set" -> Some 0 | "prop" -> Some 1 | "arr" -> Some 2 | "El" -> Some 3
  | "imp" -> Some 4 | "all" -> Some 5 | "Prf" -> Some 6 | "eq" -> Some 7
  | "or" -> Some 8 | "and" -> Some 9 | "ex" -> Some 10 | "not" -> Some 11
  | _ -> None

let name_of_index = function
  | 0 -> "Set" | 1 -> "prop" | 2 -> "arr" | 3 -> "El" | 4 -> "imp"| 5 -> "all"
  | 6 -> "Prf" | 7 -> "eq" | 8 -> "or" | 9 -> "and" | 10 -> "ex" | 11 -> "not"
  | _ -> assert false

let _ = (* sanity check *)
  for i = 0 to nb_builtins - 1 do
    assert (index_of_name (name_of_index i) = Some i)
  done

let coq_name = function
  | 0 -> Some "Type" | 1 -> Some "Prop" | 2 -> Some "arr" | 4 -> Some "imp"
  | 5 -> Some "all" | 7 -> Some "eq" | 8 -> Some "or" | 9 -> Some "and"
  | 10 -> Some "ex" | 11 -> Some "not"
  | _ -> None

let builtin : (Path.t * string) array =
  let path = ["STTfa"] in
  Array.init nb_builtins (fun i -> path, name_of_index i)

let sym b = builtin.(index_of_builtin b)

let sym_map = Stdlib.ref StrMap.empty

let update_sym_map() =
  Array.iteri
    (fun i (_,n) -> sym_map := StrMap.add n (builtin_of_index i) !sym_map)
    builtin

let _ = update_sym_map()

let builtin_of_name n =
  try Some (StrMap.find n !sym_map) with Not_found -> None

(* Set renaming map from file. *)

let rmap = ref StrMap.empty

let update_rmap() =
  Array.iteri
    (fun i (_,n) ->
      match coq_name i with
      | Some s -> rmap := StrMap.add n s !rmap
      | None -> ())
    builtin

let set_renaming : string -> unit = fun f ->
  let consume = function
    | {elt=P_builtin(n,{elt=(p,s);_});_} ->
        let v = if p = [] then s else String.concat "." p ^ "." ^ s in
        rmap := StrMap.add n v !rmap
    | {pos;_} -> fatal pos "Invalid command."
  in
  Stream.iter consume (Parser.parse_file f)

(* Set renaming map from file. *)

let erase = ref StrSet.empty

let set_erasing : string -> unit = fun f ->
  let consume = function
    | {elt=P_builtin(n,{elt=(p,s);_});_} ->
        erase := StrSet.add n !erase;
        let v = if p = [] then s else String.concat "." p ^ "." ^ s in
        rmap := StrMap.add n v !rmap
    | {pos;_} -> fatal pos "Invalid command."
  in
  Stream.iter consume (Parser.parse_file f)

(* Set encoding from file. *)

let set_encoding : string -> unit = fun f ->
  let found = Array.make nb_builtins false in
  let consume = function
    | {elt=P_builtin(n,{elt;_});pos} ->
        begin match index_of_name n with
        | Some i -> builtin.(i) <- elt; found.(i) <- true
        | None -> fatal pos "Unknown builtin."
        end
    | {pos;_} -> fatal pos "Invalid command."
  in
  Stream.iter consume (Parser.parse_file f);
  Array.iteri
    (fun i b ->
      if not b then
        let pos =
          Some {fname=Some f;start_line=0;start_col=0;end_line=0;end_col=0}
        in fatal pos "Builtin %s undefined." (name_of_index i))
    found;
  update_sym_map();
  update_rmap()

(* Translation of identifiers. *)

let translate_ident : string -> string = fun s ->
  try StrMap.find s !rmap with Not_found -> s

let raw_ident : string pp = fun ppf s -> Print.uid ppf (translate_ident s)

let ident : p_ident pp = fun ppf {elt;_} -> raw_ident ppf elt

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

(* redefinition of p_get_args ignoring P_Wrap's. *)
let p_get_args : p_term -> p_term * p_term list = fun t ->
  let rec p_get_args t acc =
    match t.elt with
    | P_Appl(t, u) -> p_get_args t (u::acc)
    | P_Wrap t -> p_get_args t acc
    | _ -> t, acc
  in p_get_args t []

(* Translation of terms. *)

(* The possible priority levels are [`Func] (top level, including abstraction
   and product), [`Appl] (application) and [`Atom] (smallest priority). *)
type priority = [`Func | `Appl | `Atom]

let stt = Stdlib.ref false

let rec term : p_term pp = fun ppf t ->
  let rec atom ppf t = pp `Atom ppf t
  and appl ppf t = pp `Appl ppf t
  and func ppf t = pp `Func ppf t
  and pp priority ppf t =
    if Logger.log_enabled() then log "%a: %a" Pos.short t.pos Pretty.term t;
    match t.elt, priority with
    | P_Type, _ -> out ppf "Type"
    | P_Iden(qid,true), _ -> out ppf "@@%a" qident qid
    | P_Iden(qid,false), _ -> qident ppf qid
    | P_NLit i, _ -> raw_ident ppf i
    | P_Wild, _ -> out ppf "_"
    | P_Meta _, _ -> assert false
    | P_Patt _, _ -> assert false
    | P_Arro(a,{elt=P_Wrap b;_}), `Func
    | P_Arro(a,b), `Func -> out ppf "%a -> %a" appl a func b
    | P_Abst([x],{elt=P_Wrap t;_}), `Func ->
        out ppf "fun %a => %a" raw_params x func t
    | P_Abst([x],t), `Func ->
        out ppf "fun %a => %a" raw_params x func t
    | P_Abst(xs,t), `Func ->
        out ppf "fun%a => %a" params_list xs func t
    | P_Prod([x],{elt=P_Wrap t;_}), `Func ->
        out ppf "forall %a, %a" raw_params x func t
    | P_Prod([x],t), `Func ->
        out ppf "forall %a, %a" raw_params x func t
    | P_Prod(xs,t), `Func ->
        out ppf "forall%a, %a" params_list xs func t
    | P_LLet(x,xs,a,t,u), `Func ->
        out ppf "let %a%a%a := %a in %a"
          ident x params_list xs typopt a func t func u
    | P_Expl _, _ -> assert false
    | P_Appl({elt=P_Wrap({elt=P_Appl _;_} as a);_},b), _ ->
        pp priority ppf {t with elt=P_Appl(a,b)}
    | P_Appl(a,b), _ ->
      begin
        match p_get_args t with
        | {elt=P_Iden({elt;_},_);_}, [u]
             when !stt && (elt = sym El || elt = sym Prf) ->
            pp priority ppf u
        | {elt=P_Iden({elt;_},_);_}, [u1;u2]
             when !stt && (elt = sym Arr || elt = sym Imp) ->
            pp priority ppf {t with elt=P_Arro(u1,u2)}
        | {elt=P_Iden({elt;_},_);_},
          [{elt=P_Wrap({elt=P_Abst([_] as xs,u);_});_}]
             when !stt && elt = sym All ->
            pp priority ppf {t with elt=P_Prod(xs,u)}
        | {elt=P_Iden({elt;_},_);_},
          [{elt=P_Wrap({elt=P_Abst([x],u);_});_}]
             when !stt && elt = sym Ex ->
            out ppf "exists %a, %a" raw_params x func u
        | {elt=P_Iden({elt;_},false);_}, [u;v] when !stt && elt = sym Eq ->
            out ppf "%a = %a" func u func v
        | {elt=P_Iden({elt;_},false);_}, [u;v] when !stt && elt = sym Or ->
            out ppf "%a \\/ %a" func u func v
        | {elt=P_Iden({elt;_},false);_}, [u;v] when !stt && elt = sym And ->
            out ppf "%a /\\ %a" func u func v
        | {elt=P_Iden({elt;_},false);_}, [u] when !stt && elt = sym Not ->
            out ppf "~ %a" appl u
        | _ ->
            if priority = `Atom then out ppf "(%a %a)" appl a atom b
            else out ppf "%a %a" appl a atom b
      end
    | P_Wrap t, _ -> out ppf "(%a)" func t
    | _ -> out ppf "(%a)" func t
  in
  let rec toplevel ppf t =
    match t.elt with
    | P_Abst([x],t) -> out ppf "fun %a => %a" raw_params x toplevel t
    | P_Abst(xs,t) -> out ppf "fun%a => %a" params_list xs toplevel t
    | P_Prod([x],t) -> out ppf "forall %a, %a" raw_params x toplevel t
    | P_Prod(xs,t) -> out ppf "forall%a, %a" params_list xs toplevel t
    | P_Arro(a,b) -> out ppf "%a -> %a" appl a toplevel b
    | P_LLet(x,xs,a,t,u) ->
        out ppf "let %a%a%a := %a in %a"
          ident x params_list xs typopt a toplevel t toplevel u
    | P_Wrap u -> toplevel ppf u
    | P_Appl({elt=P_Iden({elt;_},_);_}, u)
         when !stt && (elt = sym El || elt = sym Prf) -> toplevel ppf u
    | _ -> func ppf t
  in
  toplevel ppf t

and raw_params : p_params pp = fun ppf (ids,t,_) ->
  match t with
  | Some t -> out ppf "%a : %a" param_ids ids term t
  | None -> param_ids ppf ids

and params : p_params pp = fun ppf ((ids,t,b) as x) ->
  match b, t with
  | true, _ -> out ppf "{%a}" raw_params x
  | false, Some _ -> out ppf "(%a)" raw_params x
  | false, None -> param_ids ppf ids

(* starts with a space if the list is not empty *)
and params_list : p_params list pp = fun ppf ->
  List.iter (out ppf " %a" params)

(* starts with a space if <> None *)
and typopt : p_term option pp = fun ppf t ->
  Option.iter (out ppf " : %a" term) t

(* Translation of commands. *)

let is_lem x = is_opaq x || is_priv x

let command : p_command pp = fun ppf { elt; _ } ->
  begin match elt with
  | P_inductive _ -> assert false
  | P_open ps -> out ppf "Import %a@." (List.pp path " ") ps
  | P_require (true, ps) ->
      out ppf "Require Import %a.@." (List.pp path " ") ps
  | P_require (false, ps) ->
      out ppf "Require %a." (List.pp path " ") ps
  | P_require_as (p,i) -> out ppf "Module %a := %a.@." ident i path p
  | P_symbol
    { p_sym_mod; p_sym_nam; p_sym_arg; p_sym_typ;
      p_sym_trm; p_sym_prf=_; p_sym_def } ->
      if not (StrSet.mem p_sym_nam.elt !erase) then
        begin match p_sym_def, p_sym_trm, p_sym_arg, p_sym_typ with
          | true, Some t, _, _ ->
              if List.exists is_lem p_sym_mod then
                out ppf "Lemma %a%a%a.\nProof. exact (%a). Qed.@."
                  ident p_sym_nam params_list p_sym_arg typopt p_sym_typ
                  term t
              else
                out ppf "Definition %a%a := %a.@."
                  ident p_sym_nam params_list p_sym_arg term t
          | false, _, [], Some t ->
              out ppf "Axiom %a : %a.@." ident p_sym_nam term t
          | false, _, _, Some t ->
              out ppf "Axiom %a : forall%a, %a.@."
                ident p_sym_nam params_list p_sym_arg term t
          | _ -> assert false
        end
  | _ -> if !stt then () else assert false
  end

let ast : ast pp = fun ppf -> Stream.iter (command ppf)

(* Set requiring from file. *)

let require = ref None

let set_requiring : string -> unit = fun f -> require := Some f

let print : ast -> unit = fun s ->
  begin match !require with
  | Some f ->
      out std_formatter "Require Import %s.\n" (Filename.chop_extension f)
  | None -> ()
  end;
  ast std_formatter s
