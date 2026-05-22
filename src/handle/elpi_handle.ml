open Elpi.API
open Core
open Elpi_lambdapi

let ss_component : Sig_state.t State.component =
  State.declare_component ~name:"elpi:ss"
    ~pp:(fun _fmt _ -> ()) ~init:(fun () -> Sig_state.dummy) ~start:(fun x -> x) ()

let goalc = RawData.Constants.declare_global_symbol "goal"
let nablac = RawData.Constants.declare_global_symbol "nabla"
let sealc = RawData.Constants.declare_global_symbol "seal"
let msolvec = RawData.Constants.declare_global_symbol "msolve"
let compilec = RawData.Constants.declare_global_symbol "compile"

let embed_goal : Term.meta Conversion.embedding = fun ~depth st m ->
  let open Term in
  let ty =
    let open Timed in
    !(m.meta_type) in 

  let open RawData in
  (*let open Utils in*)
  (*Common.Console.out 1 "BEFORE EMBED GOAL:@ %a@\n" Print.term ty;*)

  let rec aux ~depth st (c,i,args) ty =
    match unfold ty with
    | Prod (dom,b) ->
      (*Common.Console.out 1 "EMBED HYP:@ %a@\n" Print.term dom;*)
      let st, dom, gls = embed_term ~ctx:c ~depth st dom in
      let x,b,c = Ctxt.unbind ~keep:true c depth None b in
      let st, g, gls1 =
        aux ~depth:(depth+1) st
          (c,i,x::args) b in
      st, mkApp nablac dom [mkLam g], gls @ gls1
    | _ ->
       (*Common.Console.out 1 "EMBED CONCL:@ %d %d |- %a@\n" (List.length c) (List.length ctx) Print.term ty;*)
       (*let ctx = List.map (fun (from,t) -> move ~from ~to_:depth t) ctx in*)
       let st, ty, gls = embed_term ~ctx:c ~depth st ty in
       let args = List.rev args |> List.map Term.mk_Vari in
       let args1,args2 = Lplib.List.cut args (i.Term.meta_arity) in
       let m = Term.add_args (mk_Meta (i, args1 |> Array.of_list)) args2 in
       let st, i, gls1 = embed_term ~ctx:c ~depth st m in
       st, mkApp sealc (mkApp goalc (*(list_to_lp_list ctx)*) ty [i]) [], gls @ gls1
  in
  let rc = aux ~depth st ([],m,[]) ty in
  (*Common.Console.out 1 "EMBED GOAL END ------------:@ %a@\n" Print.term ty;*)
  rc
   
let goal : Term.meta Conversion.t = {
  Conversion.embed = embed_goal;
  readback = (fun ~depth:_ _ _ -> assert false);
  pp_doc = (fun fmt _ -> Format.fprintf fmt "TODO");
  pp = (fun fmt _ -> Format.fprintf fmt "TODO");
  ty = Conversion.TyName "sealed-goal"
}

(** APIs (data types and predicates) exposed to Elpi *)
let lambdapi_builtin_declarations : BuiltIn.declaration list =
  let open BuiltIn in
  let open BuiltInPredicate in
  let open BuiltInData in
  let open BuiltInPredicate.Notation in
[
  LPDoc "---- Lambdapi datatypes ----";

  MLData sym;
  MLData term;
  LPCode {|
kind sealed-goal type.
external symbol nabla : term -> (term -> sealed-goal) -> sealed-goal = "0".
external symbol seal : goal -> sealed-goal = "0".

kind goal type.
external symbol goal : term -> term -> goal = "0".

external pred msolve i:list sealed-goal o:list (option term).
  
|};

  LPDoc "---- Builtin predicates ----";

  MLCode(Pred("lp.sig",
    In(sym,"S",
    Out(term,"T",
    Easy "Gives the type of a symbol")),
    (fun s _ ~depth:_ -> !: (Timed.(!) s.Term.sym_type))),
    DocAbove);

  (*MLCode(Pred("lp.tc-instances",
    Out(list sym,"L",
    Read (ContextualConversion.unit_ctx, "Gives the list of type class instances")),
    (fun _ ~depth:_ _ _ state ->
      let s = State.get ss_component state in
      !: (s.Sig_state.active_tc_inst |> Term.SymSet.elements))),
    DocAbove);*)

  MLCode(Pred("lp.tc?",
    In(sym,"S",
    Read (ContextualConversion.unit_ctx, "Tells if S is a type class")),
    (fun sym ~depth:_ _ _ state ->
      let s = State.get ss_component state in
      if (s.Sig_state.active_tc |> Term.SymSet.mem sym) then ()
      else raise No_clause)),
    DocAbove);

  MLCode(Pred("lp.snf",
    In(term,"X",
    Out(term,"SX",
    Read (ContextualConversion.unit_ctx, "SX is the snf of X"))),
    (fun t _ ~depth:_ _ _ _ ->
      !: (Eval.snf ~tags:[`NoExpand] [] t))),
    DocAbove);

  MLCode(Pred("lp.eq_modulo",
    In(term,"X",
    In(term,"Y",
    Read (ContextualConversion.unit_ctx, "X = Y upto rewrite"))),
    (fun x y ~depth:_ _ _ _ ->
      if Eval.pure_eq_modulo [] x y then () else raise No_clause)),
    DocAbove);

  MLCode(Pred("lp.unif",
    In(term,"X",
    In(term,"Y",
    Read (ContextualConversion.unit_ctx, "unify X with Y"))),
    (fun x y ~depth:_ _ _ state ->
      let problem = State.get pb state in
      let open Timed in
      (* CSC: empty context is bad here *)
      Common.Console.out 1 "\n***UNIF before: %a == %a\n" Print.term x Print.term y;
      assert (List.length !problem.Term.unsolved = 0);
      problem := Term.{ !problem with to_solve = ([],x,y)::!problem.to_solve } ;
      if Unif.solve_noexn problem then begin
       assert (List.length !problem.Term.unsolved = 0);
       Common.Console.out 1 "\n***UNIF after: %a == %a\n" Print.term x Print.term y;
       ()
      end else raise No_clause)),
    DocAbove);

  MLCode(Pred("lp.term->string",
    In(term,"T",
    Out(string,"S",
    Easy "Pretty prints a term T to the string S")),
    (fun t _ ~depth:_ -> !: (Format.asprintf "%a" Print.term t))),
    DocAbove);

  LPDoc "---- Elpi predicates ----";

] @ Elpi.Builtin.std_declarations

let lambdapi_builtins =
  BuiltIn.declare ~file_name:"lambdap.elpi" lambdapi_builtin_declarations

let document () =
  BuiltIn.document_file ~header:"% automatically generated" lambdapi_builtins

(** The runtime of Elpi (we need only one I guess) *)
let elpi = ref None

let init () =
(* let cwd = Filename.concat (Sys.getcwd()) "." in
 let root = match Parsing.Package.find_config cwd with
  | None           -> Common.Error.wrn None "%s" (Option.get !Common.Library.lib_root);
                      let getfile s = Common.Library.file_of_path (Common.Library.path_of_file Parsing.LpLexer.escape s) in
                      Common.Error.wrn None "%s" (getfile "tests/OK/elpitest.lp") ; cwd
  | Some(cfg_file) -> Filename.dirname cfg_file in*)
  let root = "/home/agontard/lambdapi/tests" in
  Setup.set_warn (fun ?loc:_~id s -> match id with Setup.UndeclaredGlobal -> Common.Error.fatal None "%s" s | _ -> Common.Error.wrn None "%s" s);
  let e = Setup.init
    ~builtins:[lambdapi_builtins]
    ~file_resolver:(Parse.std_resolver ~paths:[root] ()) () in
  elpi := Some e;
  document ()

let rec ensure_initialized () =
  match !elpi with
  | None -> init (); assert (!elpi <> None) ; ensure_initialized ()
  | Some e -> e

(** Given an Elpi file, a predicate name and a Terms.term argument we
    run Elpi and print the term before/after the execution  *)
let run : Sig_state.t -> string -> string -> Parsing.Syntax.p_term -> unit =
fun ss file predicate arg ->
  let pos = arg.Common.Pos.pos in
  (* let loc = Elpi_AUX.loc_of_pos pos in *)
  let arg = Parsing.Scope.scope_term false ss Env.empty arg in
  let elpi = ensure_initialized () in

  let ast = Parse.program ~elpi ~file in
  let prog =
    let flags = Elpi.API.Compile.default_flags in
    match Elpi.API.Compile.scope_ast ~flags ~elpi ast with
    | [ x ] ->
      let base = Elpi.API.Compile.(empty_base ~elpi) in
      let unit = Elpi.API.Compile.unit ~flags ~elpi ~base x in
      Elpi.API.Compile.extend ~flags ~base unit
    | _ -> Common.Error.fatal pos "elpi: accumulate not supported" in
  let query st =
    let open Elpi.API.RawData in
    let st = State.set ss_component st ss in
    let st, arg, gls = Elpi_lambdapi.embed_term ~depth:0 st arg in
    let st, v = Elpi.API.FlexibleData.Elpi.make ~name:"Result" st in
    let v = mkUnifVar v ~args:[] st in
    let predicate = Elpi.API.RawQuery.global_name_to_constant st predicate in
    st, mkAppGlobal predicate arg [v] , gls in
    (* predicate; arguments = (D(term,arg,Q(term,"it",N))) }) in *)
  let query = Elpi.API.RawQuery.compile_raw_term prog query in

  Common.Console.out 1 "\nelpi: before: %a\n" Print.term arg;
  match Execute.once (Elpi.API.Compile.optimize query) with
  | Execute.Success {
      Data.state; pp_ctx; constraints; assignments; _
    } ->
      let _ = readback_assignments state in
      let arg1 = Elpi.API.Setup.StrMap.find "Result" assignments in
      let _, arg1, _ = Elpi_lambdapi.readback_term ~depth:0 state arg1 in
      Common.Console.out 1 "\nelpi: after: %a\n" Print.term arg1;
      Common.Console.out 1 "elpi: constraints:@ @[<v>%a@]\n"
        Pp.(constraints pp_ctx) constraints
  | Failure -> Common.Error.fatal_no_pos "elpi: failure"
  | NoMoreSteps -> assert false

let extend (cctx) v ?def ty = (v, ty, def) :: cctx

let tc_solver_prog =
  try (
  let elpi = ensure_initialized() in
  let file = "tcsolver.elpi" in
  let ast = Parse.program ~elpi ~file in
  let flags = Elpi.API.Compile.default_flags in
  match Elpi.API.Compile.scope_ast ~flags ~elpi ast with
  | [ x ] ->
    let base = Elpi.API.Compile.(empty_base ~elpi) in
    let unit = Elpi.API.Compile.unit ~flags ~elpi ~base x in
    Elpi.API.Compile.extend ~flags ~base unit
  | _ -> Common.Error.fatal_no_pos "elpi: accumulate not supported")
  with
  | Elpi.API.Parse.ParseError(l,m) -> Common.Error.fatal None "%s" (Elpi.API.Ast.Loc.show l ^ "\n" ^ m)
  | Elpi.API.Compile.CompileError(l,m) -> begin match l with | Some l -> Common.Error.fatal None "%s" (Elpi.API.Ast.Loc.show l ^ "\n" ^ m)
    | _ -> Common.Error.fatal None "%s" m end

let add_tc_instance : Sig_state.t -> Common.Pos.popt -> Term.sym -> Elpi.API.Compile.program -> Elpi.API.Compile.program =
  fun ss pos sym base ->
  let query st =
    let open Elpi.API.RawData in
    let st = State.set ss_component st ss in
    let st, v = Elpi.API.FlexibleData.Elpi.make ~name:"Result" st in
    let v = mkUnifVar v ~args:[] st in
    let st, arg, gls = Elpi_lambdapi.sym.Conversion.embed ~depth:0 st sym in
    st, mkAppGlobal compilec arg [v] , gls in
    (* predicate; arguments = (D(term,arg,Q(term,"it",N))) }) in *)
  let query = Elpi.API.RawQuery.compile_raw_term tc_solver_prog query in
  (*let () = Format.eprintf "%a\n%!" Elpi.API.Pp.program tc_solver_prog in*)
  (*let _ = Setup.trace ["-trace-on";"-trace-at";"1";"9999";"-trace-only";"\\(run\\|select\\|user:\\)"] in*)
  match Execute.once (Elpi.API.Compile.optimize query) with
  | Execute.Success {
      Data.state; pp_ctx; (*constraints;*) assignments; _
    } ->
      let _ = readback_assignments ~pos state in
      let arg1 = Elpi.API.Setup.StrMap.find "Result" assignments in
      let loc : Ast.Loc.t = Elpi_AUX.loc_of_popt pos in
      let ast = Elpi.API.Utils.clause_of_term ~pp_ctx ~depth:0 loc arg1 in
      (*let () = Format.eprintf "%a\n%!" Elpi.API.Pp.Ast.program ast in*)
      let flags = Elpi.API.Compile.default_flags in
      let elpi = ensure_initialized() in
      begin match Elpi.API.Compile.scope_ast ~flags ~elpi ast with
      | [ x ] ->
        let unit = Elpi.API.Compile.unit ~flags ~elpi ~base x in
        Elpi.API.Compile.extend ~flags ~base unit
      | _ -> Common.Error.fatal pos "elpi: accumulate not supported"
      end
  | Failure -> Common.Error.fatal pos "elpi: failure in add_instance"
  | NoMoreSteps -> assert false

let is_tc_instance : Sig_state.t -> Term.ctxt -> Term.meta -> bool =
  fun ss c m ->
  let open Timed in
  let open Term in
  let is_tc symb  =
    SymSet.mem symb !(ss.Sig_state.signature.Sign.sign_tc) in
  let rec aux c t =
    match get_args (unfold t) with
    | Symb s, _ -> is_tc s
    | Prod(dom, b), [] ->
      let (x, b) = unbind b in
      let c = extend c x dom in
      aux c b
    | _ -> false
  in
    aux c !(m.meta_type)

let metas_of_term : Term.ctxt -> Term.term -> Term.meta list =
  fun c t ->
  let open Term in
  let acc = ref [] in
  let rec aux c t =
    match unfold t with
    | Meta(m,_) when not (List.memq m !acc) ->
       acc := m :: !acc
    | Abst (dom, b) | Prod(dom, b) ->
       aux c dom;
       let (x, b) = unbind b in
       let c = extend c x dom in
       aux c b
    | LLet (dom, t, b) ->
       aux c dom;
       aux c t;
       let (x, b) = unbind b in
       let c = extend c x dom in
       aux c b
    | Appl(t,u) -> aux c t; aux c u
    | Plac _ -> assert false (* term was inferred before *)
    | _ -> ()
  in
    aux c t;
    !acc

(** [meta_map_term t] replaces each subterm of [t] of the form [Term.Meta (m,args)] with [f m args] *)
let rec meta_map_term : (Term.meta -> Term.term array -> Term.term) -> Term.term -> Term.term =
  fun f t -> let open Term in
  let cont = meta_map_term f in
  let bcont = binder cont in
  match t with
  | Meta(m,args) -> f m args
  | Abst(dom,b) -> let dom = cont dom in let b = bcont b in mk_Abst(dom,b)
  | Prod(dom,b) -> let dom = cont dom in let b = bcont b in mk_Prod(dom,b)
  | LLet(dom,t,b) -> let dom = cont dom in let t = cont t in let b = bcont b in
    mk_LLet(dom,t,b)
  | Appl(t,u) -> let t = cont t in let u = cont u in mk_Appl(t,u)
  | _ -> t

let scope_ref : (Parsing.Syntax.p_term -> Term.term * (int * string) list) ref = ref (fun _ -> assert false)

(* we set the state, Elpi.API.Query lacks this function *)

let trace = Common.Console.register_flag "elpi-trace" false

let solve_tc : ?scope:(Parsing.Syntax.p_term -> Term.term * (int * string) list) -> Sig_state.t -> Common.Pos.popt -> Term.problem -> Term.ctxt ->
  Term.term * Term.term -> Term.term * Term.term =
  fun ?scope ss pos _pb ctxt (t,ty) ->
    let tc = metas_of_term ctxt t in
    if tc == [] then (t,ty) else begin
      Option.iter (fun f -> scope_ref := f) scope;

      (*Common.Console.out 1 "BEFORE TC RESOLUTION:@ %a : %a@\n" Print.term t Print.term ty;
      List.iter
        (fun m ->
          Common.Console.out 1 "META TY:@ %d : %a@\n" m.Term.meta_key Print.term (Timed.(!(m.Term.meta_type))))
          tc;*)
      let query st =
        let open Elpi.API.RawData in
        let st = State.set ss_component st ss in
        let st, v = Elpi.API.FlexibleData.Elpi.make ~name:"Result" st in
        let v = mkUnifVar v ~args:[] st in
        let st, arg, gls = Elpi.API.Utils.map_acc (goal.embed ~depth:0) st tc in
        st, mkAppGlobalL msolvec [Elpi.API.Utils.list_to_lp_list arg; v], gls in
      let query = Elpi.API.RawQuery.compile_raw_term (Sig_state.get_solver ss pos) query in

      if Timed.(!trace) then (let _ = Setup.trace ["-trace-on";"json";"/tmp/rawtrace.json";"-trace-at";"1";"9999";"-trace-only";"user"] in ());
      match Execute.once (Elpi.API.Compile.optimize query) with
      | Execute.Success { Data.state; assignments; _} ->
          (*let _ = readback_assignments ~pp_ctx:(Some pp_ctx) ~pos state in*)
          let insts = Elpi.API.Setup.StrMap.find "Result" assignments in
          let insts = Elpi.API.Utils.lp_list_to_list ~depth:0 insts in
          let _,insts,_ = Elpi.API.Utils.map_acc ((Elpi.Builtin.option term).readback ~depth:0) state insts in
          let fill_meta m' = Option.map (List.nth insts)
            (List.find_index (fun m -> Term.(m.meta_key = m'.meta_key)) tc)
          in
          let inst_meta m args = match fill_meta m with
            | Some (Some t) -> Eval.snf_beta (Term.add_args t (Array.to_list args))
            | _ -> Term.mk_Meta(m,args)
          in
          let res = meta_map_term inst_meta t in
          (res,ty)
      | Failure -> (t,ty)
        (* Common.Error.fatal_no_pos "elpi: failure" *)
      | NoMoreSteps -> assert false
    end

let tc_solve_problem : ?scope: (Parsing.Syntax.p_term -> Term.term * (int * string) list) -> ?additional_goals: Goal.goal list -> Sig_state.t -> Common.Pos.popt -> Term.problem -> Goal.goal list =
  fun ?scope ?(additional_goals=[]) ss pos p ->
  let open Goal in
  let open Term in
  let open Common.Error in
  let open Timed in
  if not (Unif.solve_noexn p) then
    fatal pos "Unification goals are unsatisfiable.";
  let try_solvetc g = match g with
    | Typ gt as g -> let goal_term = mk_Meta(gt.goal_meta,Env.to_terms gt.goal_hyps) in
      let t,_ = solve_tc ?scope ss pos p (ctxt g) (goal_term,gt.goal_type) in
      if match t with Meta _ -> false | _ -> true then
        begin match Infer.check_noexn p (ctxt g) t gt.goal_type with
        | Some res when Unif.solve_noexn p ->
          (*TODO: do I need to do that actually ? or perhaps only once at the end.
                  Though accidentally, it looks like it is useful. *)
          p := {!p with recompute = true};
          gt.goal_meta.meta_value := Some (bind_mvar (Env.vars gt.goal_hyps) res)
        | _ -> fatal pos "typeclass solver error: could not check %a : %a"
               Print.term t Print.term gt.goal_type end
    | _ -> ()
    in
  let is_eq_goal_meta m = function
    | Typ gt -> m == gt.goal_meta
    | _ -> assert false
  in
  let add_goal m gs =
    if List.exists (is_eq_goal_meta m) gs then gs
    else Goal.of_meta m :: gs
  in
  (* try solving the remaining goals, and in case of progress, re-trigger unification. *)
  let all_goals = MetaSet.fold add_goal (!p).metas additional_goals in 
  List.iter try_solvetc all_goals;
  if not (Unif.solve_noexn p)
    then Common.Error.fatal pos "typeclass solver error: unification";
  let f = function
    | Typ gt -> !(gt.goal_meta.meta_value) = None
    | Unif _ -> assert false in
  List.filter f all_goals @ (List.map (fun c -> Unif c) (!p).unsolved)

let embed_qterm
  : language:Elpi.API.Ast.Scope.language -> pats:(int * string) list -> Term.term -> Elpi.API.Ast.Term.t =
  fun ~language ~pats t ->
  let open Ast.Term in
  let open Term in
  let loc = Ast.Loc.initial "dummy" in
  (*Common.Console.out 1 "BEFORE EMBED:@ %a@\n" Print.term t;*)
  let rec aux t =
    (*Common.Console.out 1 "EMBED:@ %d |- %a@\n" (List.length ctx) Print.term t;*)
    match Term.unfold t with
    | Vari v ->
        mkBound ~language ~loc (Ast.Name.from_string (uniq_name v))
    | Type -> mkGlobal ~loc typec
    | Kind -> mkGlobal ~loc kindc
    | Symb s ->
        let s = csym.RawOpaqueData.cino s in
        mkAppGlobal ~loc ~hdloc:loc symbc (mkOpaque ~loc s) []
    | Prod (src, tgt) ->
        let src = aux src in
        let v,tgt = unbind tgt in
        let tgt = aux tgt in
        mkAppGlobal ~loc ~hdloc:loc prodc src
          [mkLam ~loc (Some((Ast.Name.from_string (uniq_name v),loc,language))) tgt]
    | Abst (ty, body) ->
        let src = aux ty in
        let v,tgt = unbind body in
        let tgt = aux tgt in
        mkAppGlobal ~loc ~hdloc:loc abstc src
          [mkLam ~loc (Some((Ast.Name.from_string (uniq_name v),loc,language))) tgt]
    | Appl (hd, arg) ->
        let hd = aux hd in
        let arg = aux arg in
        mkAppGlobal ~loc ~hdloc:loc applc hd [arg]
    | Meta _ -> assert false
    | Plac _ -> mkDiscard ~loc
    | Patt(Some i,_,_) -> begin
        try
          let x = List.assoc i pats in
          mkVar ~loc ~hdloc:loc (Ast.Name.from_string x) []
        with Not_found ->
          let pats = List.map (fun (i,n) -> Printf.sprintf "%d :-> %s; " i n) pats in
          Common.Error.fatal_no_pos "embed_qterm: unnamed pattern %d in map: %s" i (String.concat "" pats);
      end
    | Patt _ -> Common.Error.fatal_no_pos "embed_qterm: Patt not implemented"
    | Wild   -> Common.Error.fatal_no_pos "embed_qterm: Wild not implemented"
    | TRef _ -> Common.Error.fatal_no_pos "embed_qterm: TRef not implemented"
    | LLet _ -> Common.Error.fatal_no_pos "embed_qterm: LLet not implemented"
    | Bvar _ -> Common.Error.fatal_no_pos "embed_qterm: Bvar not implemented"
  in
  aux t


let lpq : Quotation.quotation = fun ~language _st _loc text ->
  let open Parsing in
  let ast = Parser.Lp.parse_string "xxx" ("type " ^ text ^ ";") in
  match ast |> Stream.next |> fun x -> x.Common.Pos.elt with
  | Syntax.P_query { Common.Pos.elt = Syntax.P_query_infer(t,_); _ } ->
      (*Printf.eprintf "Q %s\n" text;*)
      let t, pats = !scope_ref t in
      let t = embed_qterm ~language ~pats t in
      t
  | _ -> assert false

let () = Quotation.set_default_quotation lpq
