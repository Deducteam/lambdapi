(** functions to call the typeclass instance compiler and typeclass solver
    from tcsolver.elpi. *)
open Elpi.API
open Core
open Elpi_lambdapi

(** Typeclasses are stored in the signature state, so make it available
    in the Elpi state to allow to read them *)
let ss_component : Sig_state.t State.component =
  State.declare_component ~name:"elpi:ss"
    ~pp:(fun _fmt _ -> ()) ~init:(fun () -> Sig_state.dummy)
    ~start:(fun x -> x) ()

(** Allow elpi access to the position it is called at, so it can raise
    warnings or errors *)
let pos_component : Common.Pos.popt State.component =
  State.declare_component ~name:"elpi:pos"
    ~pp:Common.Pos.pp ~init:(fun () -> None) ~start:(fun x -> x) ()

(* The following allow to quote lambdapi terms in elpi*)

(** similar to [embed_term] but returns an Elpi.API.Ast.Term.t,
    whatever the difference might be *)
let embed_qterm
  : language:Elpi.API.Ast.Scope.language -> loc:Ast.Loc.t -> Data.state ->
    Term.term -> Elpi.API.Ast.Term.t =
  fun ~language ~loc st t ->
  let open Ast.Term in
  let open Term in
  let rec aux t =
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
          [mkLam ~loc
            (Some((Ast.Name.from_string (uniq_name v),loc,language))) tgt]
    | Abst (ty, body) ->
        let src = aux ty in
        let v,tgt = unbind body in
        let tgt = aux tgt in
        mkAppGlobal ~loc ~hdloc:loc abstc src
          [mkLam ~loc
            (Some((Ast.Name.from_string (uniq_name v),loc,language))) tgt]
    | Appl (hd, arg) ->
        let hd = aux hd in
        let arg = aux arg in
        mkAppGlobal ~loc ~hdloc:loc applc hd [arg]
    | Meta _ -> assert false
    | Plac _ -> mkDiscard ~loc
    | Patt(_,name,_) ->
      Quotation.elpi ~language:Quotation.elpi_language st loc name
    | Wild   -> Common.Error.fatal (Some (Loc.to_pos loc))
                "embed_qterm: Wild not implemented"
    | TRef _ -> Common.Error.fatal (Some (Loc.to_pos loc))
                "embed_qterm: TRef not implemented"
    | LLet _ -> Common.Error.fatal (Some (Loc.to_pos loc))
                "embed_qterm: LLet not implemented"
    | Bvar _ -> Common.Error.fatal (Some (Loc.to_pos loc))
                "embed_qterm: Bvar not implemented"
  in
  aux t

let lpq : Quotation.quotation = fun ~language st loc text ->
  let open Parsing in
  let ast = Parser.Lp.parse_string loc.source_name ("type " ^ text ^ ";") in
  match ast |> Stream.next |> fun x -> x.Common.Pos.elt with
  | Syntax.P_query { Common.Pos.elt = Syntax.P_query_infer(t,_); _ } ->
      (*Printf.eprintf "Q %s\n" text;*)
      let ss = State.get ss_component st in
      let t = Scope.scope_term_w_pats false ss [] t in
      embed_qterm ~language ~loc st t
  | _ -> assert false

let () = Quotation.set_default_quotation lpq

(** Elpi constant for the type of goals *)
let goalc = RawData.Constants.declare_global_symbol "goal"

(** Elpi constant, constructor for the [goal] type*)
let nablac = RawData.Constants.declare_global_symbol "nabla"

(** Elpi constant, constructor for the [goal] type*)
let sealc = RawData.Constants.declare_global_symbol "seal"

(** Elpi constant for the type class solver function [msolve]
    from tcsolver.elpi *)
let msolvec = RawData.Constants.declare_global_symbol "msolve"

(** Elpi constant for the type class instance compiler function [compile]
    from tcsolver.elpi *)
let compilec = RawData.Constants.declare_global_symbol "compile"

(** [embed_goal pos ~depth st m] translates the Lambdapi type of the
    metavariable [m] to an Elpi term of type [goal], returning the updated
    Elpi state [st], the translated Elpi term and an
    (I believe necessarily empty) list of conversion goals. *)
let embed_goal : Common.Pos.popt -> Term.meta Conversion.embedding =
  fun pos ~depth st m ->
  let open Term in let open RawData in
  let ty =
    let open Timed in
    !(m.meta_type) in
  let rec aux ~depth st (c,i,args) ty =
    match unfold ty with
    | Prod (dom,b) ->
      let st, dom, gls = embed_term ~ctx:c pos ~depth st dom in
      let x,b,c = Ctxt.unbind ~keep:true c depth None b in
      let st, g, gls1 =
        aux ~depth:(depth+1) st
          (c,i,x::args) b in
      st, mkApp nablac dom [mkLam g], gls @ gls1
    | _ ->
       let st, ty, gls = embed_term ~ctx:c pos ~depth st ty in
       let args = List.rev args |> List.map Term.mk_Vari in
       let args1,args2 = Lplib.List.cut args (i.Term.meta_arity) in
       let m = Term.add_args (mk_Meta (i, args1 |> Array.of_list)) args2 in
       let st, i, gls1 = embed_term ~ctx:c pos ~depth st m in
       st, mkApp sealc (mkApp goalc ty [i]) [], gls @ gls1
  in
  aux ~depth st ([],m,[]) ty

(** Conversion of goal metavariables between Lambdapi and Elpi.
    It currently only allows to go from lp to elpi, as its readback
    function is not implemented *)
let goal : Term.meta Conversion.t = {
  Conversion.embed = embed_goal None;
  readback = (fun ~depth:_ _ _ -> assert false);
  pp_doc = (fun fmt _ -> Format.fprintf fmt "Lambdapi goal metavariable");
  pp = Print.meta;
  ty = Conversion.TyName "sealed-goal"
}

let pp2string pp x =
  let b = Buffer.create 80 in
  let fmt = Format.formatter_of_buffer b in
  Format.pp_set_margin fmt 80;
  Format.fprintf fmt "%a%!" pp x;
  Buffer.contents b

(** APIs (data types and predicates) exposed to Elpi *)
let lambdapi_builtin_declarations : BuiltIn.declaration list =
  let open BuiltIn in
  let open BuiltInPredicate in
  let open BuiltInData in
  let open BuiltInPredicate.Notation in
  let open ContextualConversion in
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

external pred msolve i:list sealed-goal.

|};

  LPDoc "---- Builtin predicates ----";

  MLCode(Pred("lp.sig",
    In(sym,"S",
    Out(term,"T",
    Easy "Gives the type of a symbol")),
    (fun s _ ~depth:_ -> !: (Timed.(!) s.Term.sym_type))),
    DocAbove);

  MLCode(Pred("lp.wrn",
    VariadicIn(unit_ctx, !> any, "Prints a generic warning message"),
  (fun args ~depth _hyps _constraints state ->
     let pp = RawPp.term depth in
     let pos = State.get pos_component state in
     Common.Error.wrn pos "%a" (RawPp.list ~boxed:true pp " ") args;
     state, (), []
     )),
  DocAbove);

  MLCode(Pred("lp.error",
    VariadicIn(unit_ctx, !> any, "Prints and *aborts* the program." ^
    " It is a fatal error for Elpi and Lambdapi"),
  (fun args ~depth _hyps _constraints state ->
     let pp = RawPp.term depth in
     let pos = State.get pos_component state in
     Common.Error.fatal pos "%s"
       (pp2string (RawPp.list ~boxed:true pp " ") args)
     )),
  DocAbove);

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
      !: (Eval.snf ~tags:[NoExpand] [] t))),
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
      assert (List.length !problem.Term.unsolved = 0);
      problem := Term.{ !problem with to_solve =
        ([],x,y)::!problem.to_solve } ;
      if Unif.solve_noexn problem then begin
        assert (List.length !problem.Term.unsolved = 0);
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

(** Path useful for Elpi *)
let elpi_path,builtins_file =
  let rec iter f n x = if n > 0 then iter f (n-1) (f x) else x in
  let exec = Sys.executable_name in
  let from_lp = Filename.concat (iter Filename.dirname 3 exec) in
  if Sys.file_exists (from_lp "src/elpi/tcsolver.elpi")
  then from_lp "src/elpi", from_lp "doc/lambdapi-builtins.elpi"
  else
  let from_opam_switch = Filename.concat (iter Filename.dirname 2 exec) in
  if Sys.file_exists (from_opam_switch "lib/lambdapi/elpi/tcsolver.elpi")
  then from_opam_switch "lib/lambdapi/elpi", ""
  else assert false

(** Expose them to Elpi. *)
let lambdapi_builtins =
  BuiltIn.declare ~file_name:builtins_file lambdapi_builtin_declarations

(** Generates the documentation of builtin functions in file
    doc/lambdapi-builtins.elpi *)
let document () =
  BuiltIn.document_file ~header:"% automatically generated" lambdapi_builtins

(** The runtime of Elpi (we need only one I guess) *)
let elpi = ref None

(** Initialises Elpi *)
let init () =
  Setup.set_warn (fun ?loc ~id s ->
    let pos = Option.map Loc.to_pos loc in
    match id with
    | Setup.UndeclaredGlobal -> Common.Error.fatal pos "%s" s
    | _ -> Common.Error.wrn pos "%s" s);
  let e = Setup.init
    ~builtins:[lambdapi_builtins]
    ~file_resolver:(Parse.std_resolver ~paths:[elpi_path] ()) () in
  elpi := Some e

(** Sanity check + returns the Elpi setup *)
let rec ensure_initialized () =
  match !elpi with
  | None -> init (); assert (!elpi <> None) ; ensure_initialized ()
  | Some e -> e

(** The compiled content of tcsolver.elpi *)
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
  | Elpi.API.Parse.ParseError(loc,msg) ->
    Common.Error.fatal (Some (Loc.to_pos loc)) "%s" msg
  | Elpi.API.Compile.CompileError(oloc,msg) ->
    Common.Error.fatal (Option.map Loc.to_pos oloc) "%s" msg

(** If the head symbol of the conclusion of the type of [sym] is a typeclass
    in [ss], [add_tc_instance ss pos sym prog] compiles and adds a rule to
    the tc solver program [prog] declaring [sym] as an instance of that
    class. *)
let add_tc_instance : Sig_state.t -> Common.Pos.popt -> Term.sym ->
  Elpi.API.Compile.program -> Elpi.API.Compile.program =
  fun ss pos sym base ->
  let query st =
    let open Elpi.API.RawData in
    let st = State.set ss_component st ss in
    let st = State.set pos_component st pos in
    let st, v = Elpi.API.FlexibleData.Elpi.make ~name:"Result" st in
    let v = mkUnifVar v ~args:[] st in
    let st, arg, gls = Elpi_lambdapi.sym.Conversion.embed ~depth:0 st sym in
    st, mkAppGlobal compilec arg [v] , gls in
  let query = Elpi.API.RawQuery.compile_raw_term tc_solver_prog query in
  match Execute.once (Elpi.API.Compile.optimize query) with
  | Execute.Success {
      Data.state; pp_ctx; assignments; _} ->
      let _ = readback_assignments pos state in
      let arg1 = Elpi.API.Setup.StrMap.find "Result" assignments in
      let loc : Ast.Loc.t = Loc.of_popt pos in
      let ast = Elpi.API.Utils.clause_of_term ~pp_ctx ~depth:0 loc arg1 in
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

(** [metas_of_term t] Computes the list of all
    metavariables appearing in [t] *)
let metas_of_term : Term.term -> Term.meta list =
  fun t ->
  let open Term in
  let acc = ref [] in
  let rec aux t =
    match unfold t with
    | Meta(m,_) when not (List.memq m !acc) ->
       acc := m :: !acc
    | Abst (dom, b) | Prod(dom, b) ->
       aux dom;
       let (_, b) = unbind b in
       aux b
    | LLet (dom, t, b) ->
       aux dom;
       aux t;
       let (_, b) = unbind b in
       aux b
    | Appl(t,u) -> aux t; aux u
    | Plac _ -> assert false (* term was inferred before *)
    | _ -> ()
  in
    aux t;
    !acc

(** [meta_map_term t] replaces each subterm of [t] of the form
    [Term.Meta (m,args)] with [f m args] *)
let rec meta_map_term : (Term.meta -> Term.term array -> Term.term) ->
  Term.term -> Term.term =
  fun f t -> let open Term in
  let cont = meta_map_term f in
  let bcont = binder cont in
  match t with
  | Meta(m,args) -> f m args
  | Abst(dom,b) -> mk_Abst(cont dom,bcont b)
  | Prod(dom,b) -> mk_Prod(cont dom,bcont b)
  | LLet(dom,t,b) -> mk_LLet(cont dom,cont t,bcont b)
  | Appl(t,u) -> let t = cont t in let u = cont u in mk_Appl(t,u)
  | _ -> t

(** Flag "elpi_trace". When set on, calls to elpi will write the elpi
    trace in file /tmp/rawtrace.tmp.json *)
let trace = Common.Console.register_flag "elpi_trace" false

(* we set the state, Elpi.API.Query lacks this function *)
(** [solve_wit_tc ?ctxmap ss pos p] tries to solve problem [p]
    by repeatedly calling {!val:Unif.solve_noexn} and the
    typeclass solver from tcsolver.elpi until no progress can
    be made. It returns [false] if it finds a constraint it
    cannot satisfy. [ctxmap] maps meta_keys with the associated
    meta's context *)
let solve_with_tc : ?ctxtmap: Term.ctxt IntMap.t ->
    Sig_state.t -> Common.Pos.popt -> Term.problem -> bool =
  fun ?(ctxtmap=IntMap.empty) ss pos p ->
    let open Timed in
    let open Term in
    let res = ref true in
    let continue = ref true in
    while !continue && !res do
    continue := false;
    if not (Unif.solve_noexn p) then res := false else begin
    let ms = !p.metas in
    if MetaSet.is_empty ms then () else
    let tc = MetaSet.to_list ms in
      let query st =
        let open Elpi.API.RawData in
        let st = State.set ss_component st ss in
        let st = State.set pos_component st pos in
        let st, arg, gls =
          Elpi.API.Utils.map_acc (embed_goal ~depth:0 pos) st tc in
        st, mkAppGlobalL msolvec [Elpi.API.Utils.list_to_lp_list arg], gls in
      let query = Elpi.API.RawQuery.compile_raw_term
        (Sig_state.get_solver ss pos) query in
      if Timed.(!trace) then (let _ = Setup.trace
        ["-trace-on";"json";"/tmp/rawtrace.tmp.json";"-trace-at";
        "1";"9999";"-trace-only";"user"] in ());
      match Execute.once (Elpi.API.Compile.optimize query) with
      | Execute.Success { Data.state; pp_ctx; _} ->
          let _ = readback_assignments ~pp_ctx pos state in
          let instantiate_meta m =
            match !(m.Term.meta_value) with
            | Some b ->
              let vs = Array.map (fun s -> mk_Vari (new_var s))
                (mbinder_names b)
              in
              let res = msubst b vs in
              let c = ref (Option.value ~default:[]
                (IntMap.find_opt m.meta_key ctxtmap)) in
              let ty = Array.fold_left (function
              | Prod(vty,b) -> fun v ->
                c := begin match v with
                  | Vari v -> (v,vty,None)::!c
                  | _ -> assert false end;
                subst b v
              | _ -> assert false) !(m.meta_type) vs
              in
              if Unif.instantiate p !c m vs res
              then continue := true
              else Common.Error.fatal pos
                "Typeclass solver error: %s %a with %a"
                "couldn't instanciate meta of type"
                Print.term ty Print.term res
            | _ -> ()
          in
          Term.MetaSet.iter instantiate_meta ms;
      | Failure -> Common.Error.fatal pos "elpi: typeclass solver failure"
      | NoMoreSteps -> assert false
    end done;
  !res

module Sig_state = struct
  let dummy = Sig_state.of_solver tc_solver_prog add_tc_instance
  let of_sign s =
    Sig_state.of_sign_and_solver s tc_solver_prog add_tc_instance
end