(** Toplevel commands. *)

open Extra
open Timed
open Console
open Terms
open Print
open Sign
open Pos
open Files
open Syntax
open New_scope
open New_parser
module Proof = New_proof

let log_tact = Handle.log_tact

(** [handle_tactic ps tac] tries to apply the tactic [tac] (in the proof state
    [ps]), and returns the new proof state.  This function fails gracefully in
    case of error. *)
let handle_tactic : sig_state -> Proof.t -> p_tactic -> Proof.t =
    fun ss ps tac ->
  let (g, gs) =
    match Proof.(ps.proof_goals) with
    | []    -> fatal tac.pos "There is nothing left to prove.";
    | g::gs -> (g, gs)
  in
  let handle_refine : term -> Proof.t = fun t ->
    (* Obtaining the goals environment and type. *)
    let (env, a) = Proof.Goal.get_type g in
    (* Check if the goal metavariable appears in [t]. *)
    let m = Proof.Goal.get_meta g in
    log_tact "refining [%a] with term [%a]" pp_meta m pp t;
    if occurs m t then fatal tac.pos "Circular refinement.";
    (* Check that [t] is well-typed. *)
    let ctx = Ctxt.of_env env in
    log_tact "proving [%a ⊢ %a : %a]" Ctxt.pp ctx pp t pp a;
    if not (Solve.check ctx t a) then fatal tac.pos "Ill-typed refinement.";
    (* Instantiation. *)
    let vs = Array.of_list (List.map (fun (_,(x,_)) -> x) env) in
    m.meta_value := Some(Bindlib.unbox (Bindlib.bind_mvar vs (lift t)));
    (* New subgoals and focus. *)
    let metas = get_metas t in
    let new_goals = List.rev_map Proof.Goal.of_meta_decomposed metas in
    Proof.({ps with proof_goals = new_goals @ gs})
  in
  match tac.elt with
  | P_tac_refine(t)     ->
      (* Scoping the term in the goal's environment. *)
      let env = fst (Proof.Goal.get_type g) in
      let t = fst (New_scope.scope_term StrMap.empty ss env t) in
      (* Refine using the given term. *)
      handle_refine t
  | P_tac_intro(xs)     ->
      (* Scoping a sequence of abstraction in the goal's environment. *)
      let env = fst (Proof.Goal.get_type g) in
      let xs = List.map (fun x -> (x, None)) xs in
      let t = Pos.none (P_Abst(xs, Pos.none P_Wild)) in
      let t = fst (New_scope.scope_term StrMap.empty ss env t) in
      (* Refine using the built term. *)
      handle_refine t
  | P_tac_apply(t)      ->
      (* Scoping the term in the goal's environment. *)
      let env = fst (Proof.Goal.get_type g) in
      let t = Pos.none (P_Appl(t, Pos.none P_Wild)) in
      let t = fst (New_scope.scope_term StrMap.empty ss env t) in
      (* Refine using the built term. *)
      handle_refine t
  | P_tac_simpl         ->
      Proof.({ps with proof_goals = Proof.Goal.simpl g :: gs})
  | P_tac_rewrite(po,t) ->
      (* Scoping the term in the goal's environment. *)
      let env = fst (Proof.Goal.get_type g) in
      let t = fst (New_scope.scope_term StrMap.empty ss env t) in
      (* Scoping the rewrite pattern if given. *)
      let po = Option.map (New_scope.scope_rw_patt ss env) po in
      (* Calling rewriting, and refining. *)
      handle_refine (Rewrite.handle_rewrite po t)
  | P_tac_focus(i)      ->
      (* Put the [i]-th goal in focus (if possible). *)
      let rec swap i acc gs =
        match (i, gs) with
        | (0, g::gs) -> g :: List.rev_append acc gs
        | (i, g::gs) -> swap (i-1) (g::acc) gs
        | (_, _    ) -> fatal tac.pos "Invalid goal index."
      in
      Proof.{ps with proof_goals = swap i [] (g::gs)}
  | P_tac_print         ->
      (* Just print the current proof state. *)
      Console.out 1 "%a" Proof.pp ps; ps

(** [new_handle_cmd ss cmd] tries to handle the command [cmd], updating module
    state [ss] at the same time. This function fails gracefully on errors. *)
let rec new_handle_cmd : sig_state -> p_cmd loc -> sig_state = fun ss cmd ->
  let scope_basic ss t = New_scope.scope_term StrMap.empty ss Env.empty t in 
  let handle ss =
    match cmd.elt with
    | P_require(p, m)            ->
        (* Check that the module has not already been required. *)
        if PathMap.mem p !(ss.signature.deps) then
          fatal cmd.pos "Module [%a] is already required." pp_path p;
        (* Add the dependency and compile the module. *)
        ss.signature.deps := PathMap.add p [] !(ss.signature.deps);
        new_compile false p;
        (* Open or alias if necessary. *)
        begin
          match m with
          | P_require_default -> ss
          | P_require_open    ->
              let sign =
                try PathMap.find p !(Sign.loaded)
                with Not_found -> assert false (* Cannot happen. *)
              in
              open_sign ss sign
          | P_require_as(id)  ->
              let aliases = StrMap.add id.elt p ss.aliases in
              {ss with aliases}
        end
    | P_open(m)                  ->
        (* Obtain the signature corresponding to [m]. *)
        let sign =
          try PathMap.find m !(Sign.loaded) with Not_found ->
          (* The signature has nob been required... *)
          fatal cmd.pos "Module [%a] has not been required." pp_path m
        in
        (* Open the module. *)
        open_sign ss sign
    | P_symbol(ts, x, a)         ->
        (* We first build the symbol declaration mode from the tags. *)
        let m =
          match ts with
          | []              -> Defin
          | Sym_const :: [] -> Const
          | Sym_inj   :: [] -> Injec
          | _               -> fatal cmd.pos "Multiple symbol tags."
        in
        (* We scope the type of the declaration. *)
        let a = fst (scope_basic ss a) in
        (* We check that [x] is not already used. *)
        if Sign.mem ss.signature x.elt then
          fatal x.pos "Symbol [%s] already exists." x.elt;
        (* We check that [a] is typable by a sort. *)
        Solve.sort_type Ctxt.empty a;
        (* Actually add the symbol to the signature and the state. *)
        let s = Sign.add_symbol ss.signature m x a in
        {ss with in_scope = StrMap.add x.elt (s, x.pos) ss.in_scope}
    | P_rules(rs)                ->
        (* Scoping and checking each rule in turn. *)
        let handle_rule r =
          let (s,_) as r = scope_rule ss r in
          if !(s.sym_def) <> None then
            fatal_no_pos "Symbol [%a] cannot be (re)defined." pp_symbol s;
          Sr.check_rule r; r
        in
        let rs = List.map handle_rule rs in
        (* Adding the rules all at once. *)
        List.iter (fun (s,r) -> Sign.add_rule ss.signature s r) rs; ss
    | P_definition(x, xs, ao, t) ->
        (* Desugaring of arguments and scoping of [t]. *)
        let t = if xs = [] then t else Pos.none (P_Abst(xs, t)) in
        let t = fst (scope_basic ss t) in
        (* Desugaring of arguments and scoping of [ao] (if not [None]). *)
        let fn a = if xs = [] then a else Pos.none (P_Prod(xs, a)) in
        let ao = Option.map fn ao in
        let ao = Option.map (fun a -> fst (scope_basic ss a)) ao in
        (* We check that [x] is not already used. *)
        if Sign.mem ss.signature x.elt then
          fatal x.pos "Symbol [%s] already exists." x.elt;
        (* We check that [t] has a type [a], and return it. *)
        let a =
          match ao with
          | Some(a) ->
              Solve.sort_type Ctxt.empty a;
              if Solve.check Ctxt.empty t a then a else
              fatal cmd.pos "Term [%a] does not have type [%a]." pp t pp a
          | None    ->
              match Solve.infer Ctxt.empty t with
              | Some(a) -> a
              | None    -> fatal cmd.pos "Cannot infer the type of [%a]." pp t
        in
        (* Actually add the symbol to the signature. *)
        let s = Sign.add_symbol ss.signature Defin x a in
        s.sym_def := Some(t);
        {ss with in_scope = StrMap.add x.elt (s, x.pos) ss.in_scope}
    | P_theorem(x, a, ts, pe)    ->
        (* Scoping the type (statement) of the theorem, check sort. *)
        let a = fst (scope_basic ss a) in
        Solve.sort_type Ctxt.empty a;
        (* We check that [x] is not already used. *)
        if Sign.mem ss.signature x.elt then
          fatal x.pos "Symbol [%s] already exists." x.elt;
        (* Act according to the ending state. *)
        begin
          match pe with
          | P_proof_abort ->
              (* Just ignore the command, with a warning. *)
              wrn "[%a] Proof aborted.\n" Pos.print cmd.pos; ss
          | P_proof_admit ->
              (* Initialize the proof and plan the tactics. *)
              let st = Proof.init x a in
              let st = List.fold_left (handle_tactic ss) st ts in
              (* If the proof is finished, display a warning. *)
              if Proof.finished st then
                wrn "[%a] Proof can be terminated." Pos.print cmd.pos;
              (* Add a symbol corresponding to the proof, with a warning. *)
              let s = Sign.add_symbol ss.signature Const x a in
              wrn "[%a] Proof admitted.\n" Pos.print cmd.pos;
              {ss with in_scope = StrMap.add x.elt (s, x.pos) ss.in_scope}
          | P_proof_QED   ->
              (* Initialize the proof and plan the tactics. *)
              let st = Proof.init x a in
              let st = List.fold_left (handle_tactic ss) st ts in
              (* Check that the proof is indeed finished. *)
              if not (Proof.finished st) then
                fatal cmd.pos "The proof is not finished.";
              (* Add a symbol corresponding to the proof. *)
              let s = Sign.add_symbol ss.signature Const x a in
              {ss with in_scope = StrMap.add x.elt (s, x.pos) ss.in_scope}
        end
    | P_assert(mf, asrt)         ->
        let test_type =
          match asrt with
          | P_assert_typing(t,a) ->
              let t = fst (scope_basic ss t) in
              let a = fst (scope_basic ss a) in
              Handle.HasType(t, a)
          | P_assert_conv(t,u)   ->
              let t = fst (scope_basic ss t) in
              let u = fst (scope_basic ss u) in
              Handle.Convert(t, u)
        in
        Handle.(handle_test {is_assert = true; must_fail = mf; test_type}); ss
    | P_set(P_config_debug(e,s)) ->
        (* Just update the option, state not modified. *)
        Console.set_debug e s; ss
    | P_set(P_config_verbose(i)) ->
        (* Just update the option, state not modified. *)
        Console.verbose := i; ss
  in
  handle ss

(** [compile force path] compiles the file corresponding to [path], when it is
    necessary (the corresponding object file does not exist,  must be updated,
    or [force] is [true]).  In that case,  the produced signature is stored in
    the corresponding object file. *)
and new_compile : bool -> Files.module_path -> unit =
  fun force path ->
  let base = String.concat "/" path in
  let src = base ^ Files.new_src_extension in
  let obj = base ^ Files.new_obj_extension in
  if not (Sys.file_exists src) then fatal_no_pos "File [%s] not found." src;
  if List.mem path !loading then
    begin
      fatal_msg "Circular dependencies detected in [%s].\n" src;
      fatal_msg "Dependency stack for module [%a]:\n" Files.pp_path path;
      List.iter (fatal_msg "  - [%a]\n" Files.pp_path) !loading;
      fatal_no_pos "Build aborted."
    end;
  if PathMap.mem path !loaded then
    out 2 "Already loaded [%s]\n%!" src
  else if force || Files.more_recent src obj then
    begin
      let forced = if force then " (forced)" else "" in
      out 2 "Loading [%s]%s\n%!" src forced;
      loading := path :: !loading;
      let sign = Sign.create path in
      let sig_st = empty_sig_state sign in
      loaded := PathMap.add path sign !loaded;
      ignore (List.fold_left new_handle_cmd sig_st (parse_file src));
      Handle.check_end_proof (); Proofs.theorem := None;
      if Pervasives.(!Handle.gen_obj) then Sign.write sign obj;
      loading := List.tl !loading;
      out 1 "Checked [%s]\n%!" src;
    end
  else
    begin
      out 2 "Loading [%s]\n%!" src;
      let sign = Sign.read obj in
      PathMap.iter (fun mp _ -> new_compile false mp) !(sign.deps);
      loaded := PathMap.add path sign !loaded;
      Sign.link sign;
      out 2 "Loaded  [%s]\n%!" obj;
    end


