open! Lplib

open Timed
open Core
open Console
open Files

let pmap = List.pmap (fun x -> x)
let concat_map = List.concat_map

(** Representation of a single command (abstract). *)
module Command = struct
  type t = Syntax.p_command
  let equal = Syntax.eq_p_command
  let get_pos c = Pos.(c.pos)

  (*Messy pattern matching to get the qidents throughout the document*)
  let rec qidents_of_bound_p_arg (args: Syntax.p_arg)
  : Syntax.qident list * Pos.strloc list =
    match args with
    | idents , None, _ -> [], pmap idents
    | idents, Some ty,_ ->
      qidents_of_p_term ty, pmap idents

  and qidents_of_p_term (term:Syntax.p_term) = match term.elt with
    | Syntax.P_Type -> []
    | Syntax.P_Iden (qid,_ ) -> [qid]
    | Syntax.P_Wild -> []
    | Syntax.P_Meta (_, Some arr) -> let terms = Array.to_list arr in
        concat_map qidents_of_p_term terms
    | Syntax.P_Meta (_, None) -> []
    | Syntax.P_Patt (_, Some arr) -> let terms = Array.to_list arr in
        concat_map qidents_of_p_term terms
    | Syntax.P_Patt (_, None) -> []
    | Syntax.P_Appl (f, arg) ->
        (qidents_of_p_term f) @ (qidents_of_p_term arg)
    | Syntax.P_Impl (t1, t2) ->
        (qidents_of_p_term t1) @ (qidents_of_p_term t2)
    | Syntax.P_Abst (args, term) -> filter_bound_qidents args [term]
    | Syntax.P_Prod (args, term) -> filter_bound_qidents args [term]
    | Syntax.P_LLet (_,args, Some t1, t2, t3) ->
        filter_bound_qidents args [t1; t2; t3]
    | Syntax.P_LLet (_,args, None, t1, t2) ->
        filter_bound_qidents args [t1; t2]
    | Syntax.P_NLit _ -> []
    | Syntax.P_UnaO (_, term) -> qidents_of_p_term term
    | Syntax.P_BinO (t1, _, t2) -> qidents_of_p_term t1 @ qidents_of_p_term t2
    | Syntax.P_Wrap term -> qidents_of_p_term term
    | Syntax.P_Expl term -> qidents_of_p_term term

  and filter_bound_qidents
  (args : Syntax.p_arg list) (terms_list : Syntax.p_term list) =
    let qids, qargs =  List.split (List.map qidents_of_bound_p_arg args ) in
    let qids, qargs = List.concat qids, List.concat qargs in

    let args = List.map (fun (id:Syntax.ident) -> id.elt ) qargs in

    let filter_args (id : Syntax.qident) = not (List.mem (snd id.elt) args) in

    let get_qterm term = List.filter filter_args (qidents_of_p_term term) in
    let qterm = concat_map get_qterm terms_list in

  (*     Format.eprintf "Bound indetifiers :%s\n%!" (String.concat " " args);
  *)
    qids@qterm

  and qidents_of_p_config (cfg : Syntax.p_config) = match cfg with
  | Syntax.P_config_builtin (_, qid) -> [qid]
  | Syntax.P_config_unop u -> let (_, _, qid) = u in [qid]
  | Syntax.P_config_binop b -> let (_, _, _, qid) = b in [qid]
  | Syntax.P_config_ident _ -> []
  | Syntax.P_config_quant qid -> [qid]
  | Syntax.P_config_unif_rule rule -> qidents_of_p_rule rule

  and qidents_of_p_rule (rule : Syntax.p_rule) =
    let (patt, term) = rule.elt in
    (qidents_of_p_term patt)@(qidents_of_p_term term)

  let qidents_of_cmd (cmd:t) =
    match cmd.elt with
    | Syntax.P_inductive (_,_,_,_) -> []
    | Syntax.P_require (_,_) -> []
    | Syntax.P_require_as (_,_) -> []
    | Syntax.P_open _ -> []
    | Syntax.P_symbol (_, _, args, term) -> filter_bound_qidents args [term]
    | Syntax.P_rules rules -> concat_map qidents_of_p_rule rules
    | Syntax.P_definition (_pl,_b , _location , args ,Some ty, body) ->
        filter_bound_qidents args [ty; body]
    | Syntax.P_definition (_pl,_b , _location , args ,None, body) ->
        filter_bound_qidents args [body]
    | Syntax.P_theorem (_, statement, _, _) ->
        let (_, args, body) = statement.elt in
        filter_bound_qidents args [body]
    | Syntax.P_set set -> qidents_of_p_config set
    | Syntax.P_query q -> let f (q : Syntax.p_query_aux) = match q with
      | Syntax.P_query_verbose _ -> []
      | Syntax.P_query_debug (_, _) -> []
      | Syntax.P_query_flag (_, _) -> []
      | Syntax.P_query_assert (_, assertion) ->
        let g (assertion : Syntax.p_assertion) = match assertion with
          | Syntax.P_assert_typing (t1, t2) ->
              (qidents_of_p_term t1) @ (qidents_of_p_term t2)
          | Syntax.P_assert_conv (t1, t2) ->
              (qidents_of_p_term t1) @ (qidents_of_p_term t2)
        in g assertion
      | Syntax.P_query_infer (term, _) -> qidents_of_p_term term
      | Syntax.P_query_normalize (term, _) -> qidents_of_p_term term
      | Syntax.P_query_prover _ -> []
      | Syntax.P_query_prover_timeout _ -> []

      in f q.elt

  (*This function is used to get the symbol identifiers
  in the document and then create a map from them*)
  let get_qidents (doc : t) = (qidents_of_cmd doc)

end

(** Representation of a single tactic (abstract). *)
module Tactic = struct
  type t = Syntax.p_tactic
  let equal = Syntax.eq_p_tactic
  let get_pos t = Pos.(t.pos)
end

type state = Time.t * Sig_state.t

(** Exception raised by [parse_text] on error. *)
exception Parse_error of Pos.pos * string

let parse_text : state -> string -> string -> Command.t list * state =
    fun (t,st) fname s ->
  let old_syntax = Filename.check_suffix fname legacy_src_extension in
  try
    Time.restore t;
    let ast =
      if old_syntax then Legacy_parser.parse_string fname s
      else Parser.parse_string fname s
    in
    (ast, (Time.save (), st))
  with
  | Fatal(Some(Some(pos)), msg) -> raise (Parse_error(pos, msg))
  | Fatal(Some(None)     , _  ) -> assert false (* Should not produce. *)
  | Fatal(None           , _  ) -> assert false (* Should not produce. *)

type proof_finalizer = Sig_state.t -> Proof.t -> Sig_state.t
type proof_state = Time.t * Sig_state.t * Proof.t * proof_finalizer

let current_goals : proof_state -> Proof.Goal.t list = fun (_,_,p,_) ->
  p.proof_goals

type command_result =
  | Cmd_OK    of state
  | Cmd_Proof of proof_state * Tactic.t list * Pos.popt * Pos.popt
  | Cmd_Error of Pos.popt option * string

type tactic_result =
  | Tac_OK    of proof_state
  | Tac_Error of Pos.popt option * string

let t0 : Time.t Stdlib.ref = Stdlib.ref (Time.save ())

let set_initial_time : unit -> unit = fun _ ->
  Stdlib.(t0 := Time.save ())

let initial_state : file_path -> state = fun fname ->
  Console.reset_default ();
  Time.restore Stdlib.(!t0);
  Package.apply_config fname;
  let mp = Files.file_to_module fname in
  Sign.loading := [mp];
  let sign = Sig_state.create_sign mp in
  Sign.loaded  := PathMap.add mp sign !Sign.loaded;
  (Time.save (), Sig_state.of_sign sign)

let handle_command : state -> Command.t -> command_result =
    fun (st,ss) cmd ->
  Time.restore st;
  try
    let (ss, pst) = Handle.handle_cmd ss cmd in
    let t = Time.save () in
    match pst with
    | None       -> Cmd_OK(t, ss)
    | Some(data) ->
        let pst = (t, ss, data.pdata_p_state, data.pdata_finalize) in
        let ts = data.pdata_tactics in
        Cmd_Proof(pst, ts, data.pdata_stmt_pos, data.pdata_term_pos)
  with Fatal(p,m) -> Cmd_Error(p,m)

let handle_tactic : proof_state -> Tactic.t -> tactic_result = fun s t ->
  let (_, ss, p, finalize) = s in
  try
    let p = Tactics.handle_tactic ss p t in
    Tac_OK(Time.save (), ss, p, finalize)
  with Fatal(p,m) -> Tac_Error(p,m)

let end_proof : proof_state -> command_result = fun s ->
  let (_, ss, p, finalize) = s in
  try Cmd_OK(Time.save (), finalize ss p) with Fatal(p,m) -> Cmd_Error(p,m)

let get_symbols : state -> (Terms.sym * Pos.popt) Extra.StrMap.t = fun s ->
  (snd s).in_scope
