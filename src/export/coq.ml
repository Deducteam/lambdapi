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

let builtin : Term.qident array =
  let path = ["STTfa"] in
  Array.init nb_builtins (fun i -> path, name_of_index i)

let sym b = builtin.(index_of_builtin b)

(** Set renaming map from file. *)

let rmap = ref StrMap.empty

let set_renaming : string -> unit = fun f ->
  let consume = function
    | {elt=P_builtin(coq_id,{elt=([],lp_id);_});_} ->
        if Logger.log_enabled() then log "rename %s into %s" lp_id coq_id;
        rmap := StrMap.add lp_id coq_id !rmap
    | {pos;_} -> fatal pos "Invalid command."
  in
  Stream.iter consume (Parser.parse_file f)

(** Set symbols whose declarations have to be erased. *)

let erase = ref StrSet.empty

module Qid = struct type t = Term.qident let compare = Stdlib.compare end
module QidMap = Map.Make(Qid)

let map_erased_qid_coq = ref QidMap.empty

let set_erasing : string -> unit = fun f ->
  let consume = function
    | {elt=P_builtin(coq_id,lp_qid);_} ->
        if Logger.log_enabled() then
          log "rename %a into %s" Pretty.qident lp_qid coq_id;
        if Logger.log_enabled() then log "erase %s" (snd lp_qid.elt);
        erase := StrSet.add (snd lp_qid.elt) !erase;
        map_erased_qid_coq := QidMap.add lp_qid.elt coq_id !map_erased_qid_coq
    | {pos;_} -> fatal pos "Invalid command."
  in
  Stream.iter consume (Parser.parse_file f)

(** Set encoding. *)

let map_qid_builtin = ref QidMap.empty

let set_encoding : string -> unit = fun f ->
  let found = Array.make nb_builtins false in
  let consume = function
    | {elt=P_builtin(n,lp_qid);pos} ->
        begin match index_of_name n with
        | Some i ->
            if Logger.log_enabled() then
              log "builtin \"%s\" = %a" n Pretty.qident lp_qid;
            builtin.(i) <- lp_qid.elt;
            found.(i) <- true;
            let b = builtin_of_index i in
            map_qid_builtin := QidMap.add lp_qid.elt b !map_qid_builtin;
            if b = El || b = Prf then
              (if Logger.log_enabled() then log "erase %s" (snd lp_qid.elt);
               erase := StrSet.add (snd lp_qid.elt) !erase)
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
    found

(** Translation of identifiers. *)

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

(** Translation of terms. *)

let stt = Stdlib.ref false
let use_implicits = Stdlib.ref false
let use_notations = Stdlib.ref false

(* redefinition of p_get_args ignoring P_Wrap's. *)
let p_get_args : p_term -> p_term * p_term list = fun t ->
  let rec p_get_args t acc =
    match t.elt with
    | P_Appl(t, u) -> p_get_args t (u::acc)
    | P_Wrap t -> p_get_args t acc
    | _ -> t, acc
  in p_get_args t []

let app t default cases =
  let h, ts = p_get_args t in
  if !stt then
    match h.elt with
    | P_Iden({elt;_},expl) ->
        begin match QidMap.find_opt elt !map_qid_builtin with
        | None -> default h ts
        | Some builtin -> cases h ts expl builtin
        end
    | _ -> default h ts
  else default h ts

let rec term : p_term pp = fun ppf t ->
  (*if Logger.log_enabled() then
    log "pp %a" (*Pos.short t.pos*) Pretty.term t;*)
  match t.elt with
  | P_Meta _ -> wrn t.pos "TODO"; assert false
  | P_Patt _ -> wrn t.pos "TODO"; assert false
  | P_Expl _ -> wrn t.pos "TODO"; assert false
  | P_Type -> out ppf "Type"
  | P_Wild -> out ppf "_"
  | P_NLit i -> raw_ident ppf i
  | P_Iden(qid,b) ->
      if b then out ppf "@@";
      if !stt then
        match QidMap.find_opt qid.elt !map_erased_qid_coq with
        | Some s -> string ppf s
        | None -> qident ppf qid
      else qident ppf qid
  | P_Arro(u,v) -> arrow ppf u v
  | P_Abst(xs,u) -> abst ppf xs u
  | P_Prod(xs,u) -> prod ppf xs u
  | P_LLet(x,xs,a,u,v) ->
      out ppf "let %a%a%a := %a in %a"
        ident x params_list xs typopt a term u term v
  | P_Wrap u -> term ppf u
  | P_Appl _ ->
      let default h ts = out ppf "%a %a" paren h (List.pp paren " ") ts in
      app t default
        (fun h ts expl builtin ->
          match !use_notations, !use_implicits && not expl, builtin, ts with
          | _, _, (El|Prf), [u] -> term ppf u
          | _, _, (Arr|Imp), [u;v] -> arrow ppf u v
          | _, _, All, [_;{elt=P_Wrap({elt=P_Abst([_] as xs,u);_});_}]
          | _, true, All, [{elt=P_Wrap({elt=P_Abst([_] as xs,u);_});_}]
            -> prod ppf xs u
          | _, _, Ex, [_;{elt=P_Wrap({elt=P_Abst([x],u);_});_}]
          | _, true, Ex, [{elt=P_Wrap({elt=P_Abst([x],u);_});_}] ->
              out ppf "exists %a, %a" raw_params x term u
          | true, _, Eq, [_;u;v]
          | true, true, Eq, [u;v] -> out ppf "%a = %a" paren u paren v
          | true, _, Or, [u;v] -> out ppf "%a \\/ %a" paren u paren v
          | true, _, And, [u;v] ->  out ppf "%a /\\ %a" paren u paren v
          | true, _, Not, [u] -> out ppf "~ %a" paren u
          | _ -> default h ts)

and arrow ppf u v = out ppf "%a -> %a" paren u term v
and abst ppf xs u = out ppf "fun%a => %a" params_list_in_abs xs term u
and prod ppf xs u = out ppf "forall%a, %a" params_list_in_abs xs term u

and paren : p_term pp = fun ppf t ->
  let default() = out ppf "(%a)" term t in
  match t.elt with
  | P_Arro _ | P_Abst _ | P_Prod _ | P_LLet _ | P_Wrap _ -> default()
  | P_Appl _ ->
      app t (fun _ _ -> default())
        (fun _ ts _ builtin ->
          match builtin, ts with
          | (El|Prf), [u] -> paren ppf u
          | _ -> default())
  | _ -> term ppf t

and raw_params : p_params pp = fun ppf (ids,t,_) ->
  out ppf "%a%a" param_ids ids typopt t

and params : p_params pp = fun ppf ((ids,t,b) as x) ->
  match b, t with
  | true, _ -> out ppf "{%a}" raw_params x
  | false, Some _ -> out ppf "(%a)" raw_params x
  | false, None -> param_ids ppf ids

(* starts with a space if the list is not empty *)
and params_list : p_params list pp = fun ppf ->
  List.iter (out ppf " %a" params)

(* starts with a space if the list is not empty *)
and params_list_in_abs : p_params list pp = fun ppf l ->
  match l with
  | [ids,t,false] -> out ppf " %a%a" param_ids ids typopt t
  | _ -> List.iter (out ppf " %a" params) l

(* starts with a space if <> None *)
and typopt : p_term option pp = fun ppf t ->
  Option.iter (out ppf " : %a" term) t

(** Translation of commands. *)

let is_lem x = is_opaq x || is_priv x

let command : p_command pp = fun ppf {elt; pos} ->
  begin match elt with
  | P_inductive _ -> wrn pos "TODO"; assert false
  | P_open ps -> out ppf "Import %a@." (List.pp path " ") ps
  | P_require (true, ps) ->
      out ppf "Require Import %a.@." (List.pp path " ") ps
  | P_require (false, ps) ->
      out ppf "Require %a.@." (List.pp path " ") ps
  | P_require_as (p,i) -> out ppf "Module %a := %a.@." ident i path p
  | P_symbol
    { p_sym_mod; p_sym_nam; p_sym_arg; p_sym_typ;
      p_sym_trm; p_sym_prf=_; p_sym_def } ->
      if not (StrSet.mem p_sym_nam.elt !erase) then
        let p_sym_arg =
          if !stt then
            let pos = None in
            let _Set = {elt=P_Iden({elt=sym Set;pos},false);pos} in
            List.map (function ids, None, b -> ids, Some _Set, b | x -> x)
              p_sym_arg
          else p_sym_arg
        in
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
  | P_rules _ -> wrn pos "rules are not translated"
  | _ -> if !stt then () else (wrn pos "TODO"; assert false)
  end

let ast : ast pp = fun ppf -> Stream.iter (command ppf)

(** Set Coq required file. *)

let require = ref None

let set_requiring : string -> unit = fun f -> require := Some f

let print : ast -> unit = fun s ->
  begin match !require with
  | Some f ->
      out std_formatter "Require Import %s.\n" (Filename.chop_extension f)
  | None -> ()
  end;
  ast std_formatter s
