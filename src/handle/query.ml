(** Handling of queries. *)

open Common open Error open Pos
open Parsing open Syntax
open Core open Term open Print
open Proof
open Lplib open Base
open Timed

let infer : Sig_state.t -> Pos.popt -> problem -> ctxt -> term ->
  term * term =
  fun ss pos p ctx t ->
  match Infer.infer_noexn p ctx t with
  | None ->
      let ids = Ctxt.names ctx in let term = term_in ids in
      fatal pos "%a is not typable." term t
  | Some (t, a) ->
      let addmapping m = Elpi_lambdapi.IntMap.add m.meta_key ctx in
      let ctxtmap =
        MetaSet.fold addmapping !p.metas Elpi_lambdapi.IntMap.empty
      in
      if Elpi_handle.solve_with_tc ~ctxtmap ss pos p then
        begin
          if !p.unsolved = [] then (t, a)
          else
            begin
              let ids = Ctxt.names ctx in let term = term_in ids in
              List.iter (wrn pos "Cannot solve %a." constr) !p.unsolved;
              fatal pos "Failed to infer the type of %a." term t
            end
        end
      else
        let ids = Ctxt.names ctx in let term = term_in ids in
        fatal pos "%a is not typable." term t

let check : Sig_state.t -> Pos.popt -> problem -> ctxt -> term -> term ->
  term =
  fun ss pos p ctx t a ->
  let die () =
    let ids = Ctxt.names ctx in let term = term_in ids in
    fatal pos "[%a] does not have type [%a]." term t term a
  in
  match Infer.check_noexn p ctx t a with
  | Some t ->
    let addmapping m = Elpi_lambdapi.IntMap.add m.meta_key ctx in
      let ctxtmap =
        MetaSet.fold addmapping !p.metas Elpi_lambdapi.IntMap.empty
      in
    if Elpi_handle.solve_with_tc ~ctxtmap ss pos p then
      begin
        if !p.unsolved = [] then t else
          (List.iter (wrn pos "Cannot solve %a." constr) !p.unsolved;
           die ())
      end
    else die ()
  | None -> die ()

let check_sort : Sig_state.t -> Pos.popt -> problem -> ctxt -> term ->
  term * term =
  fun ss pos p ctx t ->
  match Infer.check_sort_noexn p ctx t with
  | None ->
      let ids = Ctxt.names ctx in let term = term_in ids in
      fatal pos "[%a] is not typable by a sort." term t
  | Some (t,s) ->
      let addmapping m = Elpi_lambdapi.IntMap.add m.meta_key ctx in
      let ctxtmap =
        MetaSet.fold addmapping !p.metas Elpi_lambdapi.IntMap.empty
      in
      if Elpi_handle.solve_with_tc ~ctxtmap ss pos p then
        begin
          if !p.unsolved = [] then (t, s) else
            begin
              let ids = Ctxt.names ctx in let term = term_in ids in
              List.iter (wrn pos "Cannot solve %a." constr) !p.unsolved;
              fatal pos "Failed to check that [%a] is typable by a sort."
                term s
            end
        end
      else
        let ids = Ctxt.names ctx in let term = term_in ids in
        fatal pos "[%a] is not typable by a sort." term t

(** Result of query displayed on hover in the editor. *)
type result = (unit -> string) option

(** [return pp x] prints [x] using [pp] on [Stdlib.(!out_fmt)] at verbose
   level 1 and returns a function for printing [x] on a string using [pp]. *)
let return : 'a pp -> 'a -> result = fun pp x ->
  Console.out 1 "%a" pp x;
  Some (fun () -> Format.asprintf "%a" pp x)

let status = function true -> "on" | false -> "off"

let rules sym_rule ppf s =
  match !(s.sym_rules) with
  | [] -> ()
  | r::rs ->
    let rule ppf r = sym_rule ppf (s,r) in
    let with_rule ppf r = out ppf "@.with %a" rule r in
    out ppf "rule %a%a;" rule r (List.pp with_rule "") rs

(** [handle_query ss ps q] *)
let handle : Sig_state.t -> proof_state option -> p_query -> result =
  fun ss ps {elt;pos} ->
  let env = Proof.focus_env ps in
  let mok =
    match ps with
    | None -> fun _ -> None
    | Some ps -> Proof.meta_of_key ps
  in
  let scope ?(typ=false) = Scope.scope_term ~typ ~mok true ss env in
  let ctxt = Env.to_ctxt env in
  let p = new_problem() in
  match elt with
  | P_query_print Debug ->
    let a = Logger.get_activated_loggers() in
    let f (k,d) =
      Printf.sprintf "%c: %s (%s)" k d (status (String.contains a k)) in
    return string (String.concat "\n" (List.map f (Logger.log_summary())))
  | P_query_debug(e,s) ->
      String.iter (fun c -> if Logger.is_registered c then ()
                            else fatal pos "Unknown debug flag \'%c\'" c) s;
      Logger.set_debug e s;
      Console.out 1 "debug %s%s" (if e then "+" else "-") s;
      None
  | P_query_verbose(i) ->
      let i = try int_of_string i with Failure _ ->
                fatal pos "Too big number (max is %d)." max_int in
      if i < 0 then fatal pos "Negative number.";
      if !Console.verbose = 0 then
        (Console.verbose := i; Console.out 1 "verbose %i" i)
      else (Console.out 1 "verbose %i" i; Console.verbose := i);
      None
  | P_query_print Flag ->
      let f n (_,c) l = ("flag \""^n^"\" "^status(!c)^";")::l in
      let l = Extra.StrMap.fold f Stdlib.(!Console.boolean_flags) [] in
      let l = List.sort Stdlib.compare l in
      return string (String.concat "\n" l)
  | P_query_flag(id,b) ->
      (try Console.set_flag id b
       with Not_found -> fatal pos "Unknown flag \"%s\"." id);
      Console.out 1 "flag \"%s\" %s" id (if b then "on" else "off");
      None
  | P_query_prover(s) -> Why3_tactic.default_prover := s; None
  | P_query_prover_timeout(n) ->
      let n = try int_of_string n with Failure _ ->
                fatal pos "Too big number (max is %d)" max_int in
      if n < 0 then fatal pos "Negative number";
      Why3_tactic.timeout := n;
      None
  | P_query_print Verbose ->
    return (fun ppf -> out ppf "verbose %d;") !Console.verbose
  | P_query_print Prover ->
    return (fun ppf -> out ppf "prover \"%s\";") !Why3_tactic.default_prover
  | P_query_print Prover_timeout ->
    return (fun ppf -> out ppf "prover_timeout %d;") !Why3_tactic.timeout
  | P_query_print (String s) -> return string s
  | P_query_print Coerce_rule -> return (rules sym_rule) Coercion.coerce
  | P_query_print Unif_rule ->
    let unif_rule ppf r = out ppf "%a ↪ [%a]" term (lhs r) term (rhs r) in
    return (rules unif_rule) Unif_rule.equiv
  | P_query_print Goal ->
      begin
        match ps with
        | None -> fatal pos "Not in a proof."
        | Some ps -> return Proof.goals ps
      end
  | P_query_print Builtin ->
    let def ppf n =
      match Extra.StrMap.find_opt n ss.builtins with
      | Some s -> out ppf " ≔ %a" qsym s
      | None -> ()
    in
    let f n _ acc = Format.asprintf "builtin \"%s\"%a;" n def n :: acc in
    let l = List.sort Stdlib.compare (Hashtbl.fold f Builtin.htbl []) in
    return string (String.concat "\n" l)
  | P_query_print(Symbol qid) ->
      let sym_info ppf s =
        (* Function to print a definition. *)
        let def ppf = Option.iter (out ppf "@ ≔ %a" term) in
        (* Function to print a notation *)
        let rec nota ppf n =
          match n with
          | NoNotation -> ()
          | Zero -> out ppf "@.builtin \"0\" ≔ %a;" sym s
          | Succ n -> out ppf "%a@.builtin \"+1\" ≔ %a;" nota n sym s
          | PosOne -> out ppf "@.builtin \"pos_one\" ≔ %a;" sym s
          | PosDouble -> out ppf "@.builtin \"pos_double\" ≔ %a;" sym s
          | PosSuccDouble ->
            out ppf "@.builtin \"pos_succ_double\" ≔ %a;" sym s
          | IntZero -> out ppf "@.builtin \"int_zero\" ≔ %a;" sym s
          | IntPos -> out ppf "@.builtin \"int_positive\" ≔ %a;" sym s
          | IntNeg -> out ppf "@.builtin \"int_negative\" ≔ %a;" sym s
          | n -> out ppf "@.notation %a %a;" sym s (Print.notation float) n
        in
        let notation ppf s = nota ppf !(s.sym_nota) in
        (* Function to print rules. *)
        let rules sym_rule ppf s =
          match !(s.sym_rules) with
          | [] -> ()
          | r::rs ->
            let rule ppf r = sym_rule ppf (s,r) in
            let with_rule ppf r = out ppf "@.with %a" rule r in
            out ppf "rule %a%a;" rule r (List.pp with_rule "") rs
        in
        (* Function to print a symbol declaration. *)
        let decl ppf s =
          let rules ppf s =
            if !(s.sym_rules) <> [] then out ppf "@.%a" (rules sym_rule) s in
          out ppf "%a%a%asymbol %a : %a%a;%a%a"
            expo s.sym_expo prop s.sym_prop match_strat s.sym_mstrat
            sym s sym_type s def !(s.sym_def) notation s rules s
        in
        (* Function to print constructors and the induction principle if [qid]
           is an inductive type. *)
        let ind ppf s =
          let open Sign in
          (* get the signature of [s] *)
          let sign =
            try Path.Map.find s.sym_path !loaded
            with Not_found -> assert false
          in
          try
            let ind = SymMap.find s !(sign.sign_ind) in
            let decl ppf s = out ppf "@.%a" decl s in
            List.pp decl "" ppf ind.ind_cons;
            decl ppf ind.ind_prop
          with Not_found -> ()
        in
        decl ppf s; ind ppf s
      in
      return sym_info (Sig_state.find_sym ~prt:true ~prv:true ss qid)
  | P_query_proofterm ->
      (match ps with
       | None -> fatal pos "Not in a proof"
       | Some pst ->
           match pst.proof_term with
           | Some m ->
               let ids = Env.names (Proof.focus_env ps) in
               return (term_in ids) (mk_Meta(m,[||]))
           | None -> fatal pos "Not in a definition")
  | P_query_search q ->
      let dbpath = Path.default_dbpath in
      return (Tool.Indexing.search_cmd_txt_query ss ~dbpath) q
  | P_query_assert(must_fail, P_assert_typing(pt,pa)) ->
      let t = scope pt and a = scope ~typ:true pa in
      Console.out 2 "assertion: it is %b that %a" (not must_fail)
        typing (ctxt, t, a);
      (* Check that [a] is typable by a sort. *)
      let (a, _) = check_sort ss pos p ctxt a in
      let result =
        try ignore (check ss pos p ctxt t a); true
        with Fatal _ -> false
      in
      if result = must_fail then fatal pos "Assertion failed.";
      None
  | P_query_assert(must_fail, P_assert_conv(pt,pu)) ->
      let t = scope pt and u = scope pu in
      Console.out 2 "assertion: it is %b that %a" (not must_fail)
        constr (ctxt, t, u);
      (* Check that [t] is typable. *)
      let (t, a) = infer ss pt.pos p ctxt t in
      (* Check that [u] is typable. *)
      let (u, b) = infer ss pu.pos p ctxt u in
      (* Check that [t] and [u] have the same type. *)
      p := {!p with to_solve = (ctxt,a,b)::!p.to_solve};
      if Unif.solve_noexn p then
        if !p.unsolved = [] then begin
          if Eval.eq_modulo ctxt t u = must_fail then
             fatal pos "Assertion failed."
        end else begin
          List.iter (wrn pos "Cannot solve [%a]." constr) !p.unsolved;
          fatal pos "[%a] has type [%a],@ [%a] has type [%a].@.\
                    Those two types are not unifiable."
            term t term a term u term b
        end else
          fatal pos "[%a] has type [%a],@ [%a] has type [%a].@.\
                    Those two types are not unifiable."
            term t term a term u term b;
      None
  | P_query_infer(pt, cfg) ->
      let t = scope pt in
      let t = Eval.eval cfg ctxt (snd (infer ss pt.pos p ctxt t)) in
      let ids = Env.names (Proof.focus_env ps) in
      return (term_in ids) t
  | P_query_normalize(pt, cfg) ->
      let t = scope pt in
      let t = Eval.eval cfg ctxt (fst (infer ss pt.pos p ctxt t)) in
      let ids = Env.names (Proof.focus_env ps) in
      return (term_in ids) t
