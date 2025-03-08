(** Base module for translating lp proofs encoded in simple type theory. *)

open Lplib open Extra
open Common open Pos open Error
open Parsing open Syntax
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
    | {elt=P_builtin(lean_id,{elt=([],lp_id);_});_} ->
        if Logger.log_enabled() then log "rename %s into %s" lp_id lean_id;
        rmap := StrMap.add lp_id lean_id !rmap
    | {pos;_} -> fatal pos "Invalid command."
  in
  Stream.iter consume (Parser.parse_file f)

(** Set symbols whose declarations have to be erased. *)

let erase = ref StrSet.empty

module Qid = struct type t = Term.qident let compare = Stdlib.compare end
module QidMap = Map.Make(Qid)

let map_erased_qid = ref QidMap.empty

let set_mapping : string -> unit = fun f ->
  let consume = function
    | {elt=P_builtin(lean_id,lp_qid);_} ->
        if Logger.log_enabled() then
          log "rename %a into %s" Pretty.qident lp_qid lean_id;
        let id = snd lp_qid.elt in
        if Logger.log_enabled() then log "erase %s" id;
        erase := StrSet.add id !erase;
        map_erased_qid :=
          QidMap.add lp_qid.elt lean_id !map_erased_qid;
        if fst lp_qid.elt = [] && id <> lean_id then
          rmap := StrMap.add id lean_id !rmap
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

(** Basic printing functions. We use Printf for efficiency reasons. *)

let out = Printf.printf

let char = output_char
let string = output_string

let prefix pre elt oc x = string oc pre; elt oc x
let suffix elt suf oc x = elt oc x; string oc suf

let list elt sep oc xs =
  match xs with
  | [] -> ()
  | x::xs -> elt oc x; List.iter (prefix sep elt oc) xs

(** Translation of identifiers. *)

let translate_ident : string -> string = fun s ->
  try StrMap.find s !rmap with Not_found -> s

let raw_ident oc s = string oc (translate_ident s)

let ident oc {elt;_} = raw_ident oc elt

let param_id oc idopt =
  match idopt with
  | Some id -> ident oc id
  | None    -> char oc '_'

let param_ids = list param_id " "

let raw_path = list string "."

let path oc {elt;_} = raw_path oc elt

let qident oc {elt=(mp,s);_} =
  match mp with
  | [] -> raw_ident oc s
  | _::_ -> raw_path oc mp; char oc '.'; raw_ident oc s

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

let is_lem x = is_opaq x || is_priv x

(** Set required file. *)

let require = ref None

let set_requiring : string -> unit = fun f -> require := Some f
