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
open Scope
open New_parser

(** Logging function for tactics. *)
let log_tact = new_logger 'i' "tact" "debugging information for tactics"
let log_tact = log_tact.logger

(** [gen_obj] indicates whether we should generate object files when compiling
    source files. The default behaviour is not te generate them. *)
let gen_obj = Pervasives.ref false

(** [too_long] indicates the duration after which a warning should be given to
    indicate commands that take too long to execute. *)
let too_long = Pervasives.ref infinity

(** [handle_tactic ps tac] tries to apply the tactic [tac] (in the proof state
    [ps]), and returns the new proof state.  This function fails gracefully in
    case of error. *)
let handle_tactic : sig_state -> Proof.t -> p_tactic -> Proof.t =
    fun ss ps tac ->
  (* First handle the tactics that are independant from the goal. *)
  match tac.elt with
  | P_tac_print         ->
      (* Just print the current proof state. *)
      Console.out 1 "%a" Proof.pp ps; ps
  | P_tac_proofterm     ->
      (* Just print the current proof term. *)
      let t = Eval.snf (Meta(Proof.(ps.proof_term), [||])) in
      let name = Proof.(ps.proof_name).elt in
      Console.out 1 "Proof term for [%s]: [%a]\n" name Print.pp t; ps
  | P_tac_focus(i)      ->
      (* Put the [i]-th goal in focus (if possible). *)
      let rec swap i acc gs =
        match (i, gs) with
        | (0, g::gs) -> g :: List.rev_append acc gs
        | (i, g::gs) -> swap (i-1) (g::acc) gs
        | (_, _    ) -> fatal tac.pos "Invalid goal index."
      in
      Proof.{ps with proof_goals = swap i [] ps.proof_goals}
  | _                   ->
  (* Other tactics need to act on the goal / goals. *)
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
  | P_tac_print
  | P_tac_proofterm
  | P_tac_focus(_)      -> assert false (* Handled above. *)
  | P_tac_refine(t)     ->
      (* Scoping the term in the goal's environment. *)
      let env = fst (Proof.Goal.get_type g) in
      let t = fst (Scope.scope_term StrMap.empty ss env t) in
      (* Refine using the given term. *)
      handle_refine t
  | P_tac_intro(xs)     ->
      (* Scoping a sequence of abstraction in the goal's environment. *)
      let env = fst (Proof.Goal.get_type g) in
      let xs = List.map (fun x -> (x, None)) xs in
      let t = Pos.none (P_Abst(xs, Pos.none P_Wild)) in
      let t = fst (Scope.scope_term StrMap.empty ss env t) in
      (* Refine using the built term. *)
      handle_refine t
  | P_tac_apply(t)      ->
      (* Scoping the term in the goal's environment. *)
      let env = fst (Proof.Goal.get_type g) in
      let t = Pos.none (P_Appl(t, Pos.none P_Wild)) in
      let t = fst (Scope.scope_term StrMap.empty ss env t) in
      (* Refine using the built term. *)
      handle_refine t
  | P_tac_simpl         ->
      Proof.({ps with proof_goals = Proof.Goal.simpl g :: gs})
  | P_tac_rewrite(po,t) ->
      (* Scoping the term in the goal's environment. *)
      let env = fst (Proof.Goal.get_type g) in
      let t = fst (Scope.scope_term StrMap.empty ss env t) in
      (* Scoping the rewrite pattern if given. *)
      let po = Option.map (Scope.scope_rw_patt ss env) po in
      (* Calling rewriting, and refining. *)
      handle_refine (Rewrite.rewrite ps po t)
  | P_tac_refl          ->
      handle_refine (Rewrite.reflexivity ps)
  | P_tac_sym           ->
      handle_refine (Rewrite.symmetry ps)

let parse_file = Pervasives.ref Parser.parse_file
let src_extension = Pervasives.ref Files.new_src_extension
let obj_extension = Pervasives.ref Files.new_obj_extension

(** [new_handle_cmd ss cmd] tries to handle the command [cmd], updating module
    state [ss] at the same time. This function fails gracefully on errors. *)
let rec new_handle_cmd : sig_state -> p_cmd loc -> sig_state = fun ss cmd ->
  let scope_basic ss t = Scope.scope_term StrMap.empty ss Env.empty t in
  let handle ss =
    match cmd.elt with
    | P_require(p, m)            ->
        (* Check that the module has not already been required. *)
        if PathMap.mem p !(ss.signature.sign_deps) then
          fatal cmd.pos "Module [%a] is already required." pp_path p;
        (* Add the dependency and compile the module. *)
        ss.signature.sign_deps := PathMap.add p [] !(ss.signature.sign_deps);
        compile false p;
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
          let (s,_,_) as r = scope_rule ss r in
          if !(s.sym_def) <> None then
            fatal_no_pos "Symbol [%s] cannot be (re)defined." s.sym_name;
          Sr.check_rule r; r
        in
        let rs = List.map handle_rule rs in
        (* Adding the rules all at once. *)
        List.iter (fun (s,h,r) -> Sign.add_rule ss.signature s h r.elt) rs; ss
    | P_definition(op,x,xs,ao,t) ->
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
        (* Also add its definition, if it is not opaque. *)
        if not op then s.sym_def := Some(t);
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
              wrn cmd.pos "Proof aborted."; ss
          | P_proof_admit ->
              (* Initialize the proof and plan the tactics. *)
              let st = Proof.init ss.builtins x a in
              let st = List.fold_left (handle_tactic ss) st ts in
              (* If the proof is finished, display a warning. *)
              if Proof.finished st then wrn cmd.pos "You should add QED.";
              (* Add a symbol corresponding to the proof, with a warning. *)
              let s = Sign.add_symbol ss.signature Const x a in
              wrn cmd.pos "Proof admitted.";
              {ss with in_scope = StrMap.add x.elt (s, x.pos) ss.in_scope}
          | P_proof_QED   ->
              (* Initialize the proof and plan the tactics. *)
              let st = Proof.init ss.builtins x a in
              let st = List.fold_left (handle_tactic ss) st ts in
              (* Check that the proof is indeed finished. *)
              if not (Proof.finished st) then
                fatal cmd.pos "The proof is not finished.";
              (* Add a symbol corresponding to the proof. *)
              let s = Sign.add_symbol ss.signature Const x a in
              {ss with in_scope = StrMap.add x.elt (s, x.pos) ss.in_scope}
        end
    | P_assert(must_fail, asrt)  ->
        let result =
          match asrt with
          | P_assert_typing(t,a) ->
              let t = fst (scope_basic ss t) in
              let a = fst (scope_basic ss a) in
              Solve.sort_type Ctxt.empty a;
              (try Solve.check Ctxt.empty t a with _ -> false)
          | P_assert_conv(t,u)   ->
              let t = fst (scope_basic ss t) in
              let u = fst (scope_basic ss u) in
              Eval.eq_modulo t u
        in
        if result = must_fail then fatal cmd.pos "Assertion failed."; ss
    | P_set(cfg)                 ->
        begin
          match cfg with
          | P_config_debug(e,s)     ->
              (* Just update the option, state not modified. *)
              Console.set_debug e s; ss
          | P_config_verbose(i)     ->
              (* Just update the option, state not modified. *)
              Console.verbose := i; ss
          | P_config_builtin(s,qid) ->
              (* Set the builtin symbol [s]. *)
              let sym = find_sym false ss qid in
              Sign.add_builtin ss.signature s sym;
              {ss with builtins = StrMap.add s sym ss.builtins}
        end
    | P_infer(t, cfg)            ->
        (* Infer the type of [t]. *)
        let t_pos = t.pos in
        let t = fst (scope_basic ss t) in
        let a =
          match Solve.infer [] t with
          | Some(a) -> Eval.eval cfg a
          | None    -> fatal t_pos "Cannot infer the type of [%a]." pp t
        in
        out 3 "(infr) %a : %a\n" pp t pp a; ss
    | P_normalize(t, cfg)        ->
        (* Infer a type for [t], and evaluate [t]. *)
        let t_pos = t.pos in
        let t = fst (scope_basic ss t) in
        let v =
          match Solve.infer [] t with
          | Some(_) -> Eval.eval cfg t
          | None    -> fatal t_pos "Cannot infer the type of [%a]." pp t
        in
        out 3 "(eval) %a\n" pp v; ss
  in
  try
    let (tm, ss) = time handle ss in
    if Pervasives.(tm >= !too_long) then
      wrn cmd.pos "It took %.2f seconds to handle the command." tm;
    ss
  with
  | Timeout                as e -> raise e
  | Fatal(Some(Some(_)),_) as e -> raise e
  | Fatal(None         ,m)      -> fatal cmd.pos "Error on command.\n%s" m
  | Fatal(Some(None)   ,m)      -> fatal cmd.pos "Error on command.\n%s" m
  | e                           -> let e = Printexc.to_string e in
                                   fatal cmd.pos "Uncaught exception [%s]." e

(** [compile force path] compiles the file corresponding to [path], when it is
    necessary (the corresponding object file does not exist,  must be updated,
    or [force] is [true]).  In that case,  the produced signature is stored in
    the corresponding object file. *)
and compile : bool -> Files.module_path -> unit = fun force path ->
  let base = String.concat "/" path in
  let src = base ^ Pervasives.(!src_extension) in
  let obj = base ^ Pervasives.(!obj_extension) in
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
      let parse = Pervasives.(!parse_file) in
      ignore (List.fold_left new_handle_cmd sig_st (parse src));
      if Pervasives.(!gen_obj) then Sign.write sign obj;
      loading := List.tl !loading;
      out 1 "Checked [%s]\n%!" src;
    end
  else
    begin
      out 2 "Loading [%s]\n%!" src;
      let sign = Sign.read obj in
      PathMap.iter (fun mp _ -> compile false mp) !(sign.sign_deps);
      loaded := PathMap.add path sign !loaded;
      Sign.link sign;
      out 2 "Loaded  [%s]\n%!" obj;
    end

let compile old parse b p =
  let open Pervasives in
  parse_file := parse;
  src_extension := Files.(if old then src_extension else new_src_extension);
  obj_extension := Files.(if old then obj_extension else new_obj_extension);
  compile b p
