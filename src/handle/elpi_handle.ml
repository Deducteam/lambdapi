open Elpi.API
open Core
open Elpi_lambdapi

let ss : Sig_state.t State.component =
  State.declare ~name:"elpi:ss"
    ~pp:(fun _fmt _ -> ()) ~init:(fun () -> Sig_state.dummy) ~start:(fun x -> x)

let goalc = RawData.Constants.declare_global_symbol "goal"
let ofc = RawData.Constants.declare_global_symbol "of"
let nablac = RawData.Constants.declare_global_symbol "nabla"
let sealc = RawData.Constants.declare_global_symbol "seal"

let embed_goal : Term.meta Conversion.embedding = fun ~depth st m ->
  let open Term in
  let ty =
    let open Timed in
    !(m.meta_type) in 
  let open RawData in
  let open Utils in
  let rec aux ~depth st (c,ctx,i,args) ty =
    match unfold ty with
    | Prod (dom,b) ->
      let st, dom, gls = embed_term ~ctx:c ~depth st dom in
      let x,b,c = Ctxt.unbind c depth None b in
      let st, g, gls1 =
        aux ~depth:(depth+1) st
          (c,(depth+1,mkApp ofc (mkBound depth) [dom])::ctx,i,x::args) b in
      st, mkApp nablac (mkLam g) [], gls @ gls1
    | _ ->
       let ctx = List.map (fun (from,t) -> move ~from ~to_:depth t) ctx in
       let st, ty, gls = embed_term ~ctx:c ~depth st ty in
       let m = mk_Meta (i,List.rev args |> List.map Term.of_tvar |> Array.of_list) in
       let st, i, gls1 = embed_term ~ctx:c ~depth st m in
       st, mkApp sealc (mkApp goalc (list_to_lp_list ctx) [ty; i]) [], gls @ gls1
  in
  aux ~depth st ([],[],m,[]) ty

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
type nabla (term -> sealed-goal) -> sealed-goal.
type seal goal -> sealed-goal.

kind goal type.
type goal list prop -> term -> term -> goal.

type of term -> term -> prop.

pred msolve o:list sealed-goal.
  
|};

  LPDoc "---- Builtin predicates ----";

  MLCode(Pred("lp.sig",
    In(sym,"S",
    Out(term,"T",
    Easy "Gives the type of a symbol")),
    (fun s _ ~depth:_ -> !: (Timed.(!) s.Term.sym_type))),
    DocAbove);

  MLCode(Pred("lp.tc-instances",
    Out(list sym,"L",
    Read (ContextualConversion.unit_ctx, "Gives the list of type class instances")),
    (fun _ ~depth:_ _ _ state ->
      let s = (State.get ss state).Sig_state.signature in
      !: ((Timed.(!) s.Sign.sign_tc_inst) |> Term.SymSet.elements))),
    DocAbove);

  MLCode(Pred("lp.tc?",
    In(sym,"S",
    Read (ContextualConversion.unit_ctx, "Tells if S is a type class")),
    (fun sym ~depth:_ _ _ state ->
      let s = (State.get ss state).Sig_state.signature in
      if ((Timed.(!) s.Sign.sign_tc) |> Term.SymSet.mem sym) then ()
      else raise No_clause)),
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
  let e = Setup.init
    ~builtins:[lambdapi_builtins]
    ~legacy_parser:false
    ~file_resolver:(Parse.std_resolver ~paths:[] ()) () in
  elpi := Some e;
  document ()

(** Given an Elpi file, a predicate name and a Terms.term argument we
    run Elpi and print the term before/after the execution  *)
let run : Sig_state.t -> string -> string -> Parsing.Syntax.p_term -> unit =
fun ss file predicate arg ->
  let pos = arg.Common.Pos.pos in
  let loc = Elpi_AUX.loc_of_pos pos in
  let arg = Parsing.Scope.scope_term false ss Env.empty arg in
  let elpi = match !elpi with None -> assert false | Some x -> x in

  let ast = Parse.program ~elpi ~files:[file] in
  let prog =
    let flags = Elpi.API.Compile.default_flags in
    ast |>
    Elpi.API.Compile.unit ~flags ~elpi |>
    (fun u -> Elpi.API.Compile.assemble ~elpi ~flags [u]) in

  let query =
    let open Elpi.API.Query in
    compile prog loc
      (Query { predicate; arguments = (D(term,arg,Q(term,"it",N))) }) in

  if not (Elpi.API.Compile.static_check
            ~checker:(Elpi.Builtin.default_checker ()) query) then
    Common.Error.fatal pos "elpi: type error in %s" file;

  Common.Console.out 1 "\nelpi: before: %a\n" Print.term arg;
  match Execute.once (Elpi.API.Compile.optimize query) with
  | Execute.Success {
      Data.state; pp_ctx; constraints; output = (arg1,()); _
    } ->
      let _ = readback_assignments state in
      Common.Console.out 1 "\nelpi: after: %a\n" Print.term arg1;
      Common.Console.out 1 "elpi: constraints:@ @[<v>%a@]\n"
        Pp.(constraints pp_ctx) constraints
  | Failure -> Common.Error.fatal_no_pos "elpi: failure"
  | NoMoreSteps -> assert false

let extend (cctx) v ?def ty = (v, ty, def) :: cctx

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
      let (x, b) = Bindlib.unbind b in
      let c = extend c x dom in
      aux c b
    | _ -> false
  in
    aux c !(m.meta_type)

let tc_metas_of_term : Sig_state.t -> Term.ctxt -> Term.term -> Term.meta list =
  fun ss c t ->
  let open Term in
  let acc = ref [] in
  let rec aux c t =
    match unfold t with
    | Meta(m,_) when is_tc_instance ss c m && not (List.memq m !acc) ->
       acc := m :: !acc
    | Abst (dom, b) | Prod(dom, b) ->
       aux c dom;
       let (x, b) = Bindlib.unbind b in
       let c = extend c x dom in
       aux c b
    | LLet (dom, t, b) ->
       aux c dom;
       aux c t;
       let (x, b) = Bindlib.unbind b in
       let c = extend c x dom in
       aux c b
    | Appl(t,u) -> aux c t; aux c u
    | Plac _ -> assert false (* term was inferred before *)
    | _ -> ()
  in
    aux c t;
    !acc


let scope_ref : (Parsing.Syntax.p_term -> Term.term * (int * string) list) ref = ref (fun _ -> assert false)

(* we set the state, Elpi.API.Qery lacks this function *)
let hack s c = { c with Conversion.embed =
  fun ~depth state x ->
    let state = State.set ss state s in
    c.Conversion.embed ~depth state x
}

let solve_tc : ?scope:(Parsing.Syntax.p_term -> Term.term * (int * string) list) -> Sig_state.t -> Common.Pos.popt -> Term.problem -> Term.ctxt ->
  Term.term * Term.term -> Term.term * Term.term =
  fun ?scope ss pos _pb ctxt (t,ty) ->
    let tc = tc_metas_of_term ss ctxt t in
    if tc <> [] then begin
      let elpi = match !elpi with None -> assert false | Some x -> x in
      Option.iter (fun f -> scope_ref := f) scope;

      Common.Console.out 1 "BEFORE TC RESOLUTION:@ %a : %a@\n" Print.term t Print.term ty;

      let file = "tcsolver.elpi" in
      let predicate = "msolve" in
      let pos = Elpi_AUX.loc_of_pos pos in

      let ast = Parse.program ~elpi ~files:[file] in
      let prog =
        let flags = Elpi.API.Compile.default_flags in
        ast |>
        Elpi.API.Compile.unit ~flags ~elpi |>
        (fun u -> Elpi.API.Compile.assemble ~elpi ~flags [u]) in
    
      let query =
        let open Elpi.API.Query in
        let open Elpi.API.BuiltInData in
        compile prog pos
          (Query { predicate; arguments = (D(hack ss (list goal),tc,N)) }) in
    
      if not (Elpi.API.Compile.static_check
                ~checker:(Elpi.Builtin.default_checker ()) query) then
        Common.Error.fatal_no_pos "elpi: type error in %s" file;
    
      match Execute.once (Elpi.API.Compile.optimize query) with
      | Execute.Success { Data.state; output = (); _ } ->
          let _ = readback_assignments state in
          ()
      | Failure -> Common.Error.fatal_no_pos "elpi: failure"
      | NoMoreSteps -> assert false
    end;
    t, ty

let lpq : Quotation.quotation = fun ~depth st _loc text ->
  let open Parsing in
  let ast = Parser.Lp.parse_string "xxx" ("type " ^ text ^ ";") in
  match ast |> Stream.next |> fun x -> x.Common.Pos.elt with
  | Syntax.P_query { Common.Pos.elt = Syntax.P_query_infer(t,_); _ } ->
      (*Printf.eprintf "Q %s\n" text;*)
      let t, pats = !scope_ref t in
      let st, t, _ = embed_term ~pats ~depth st t in
      st, t
  | _ -> assert false

let () = Quotation.set_default_quotation lpq
