(** Handling of queries. *)

open Common open Error open Pos
open Parsing open Syntax
open Core open Term open Print
open Proof
open Lplib open Base
open Timed

let infer : Pos.popt -> problem -> ctxt -> term -> term * term =
  fun pos p ctx t ->
  match Infer.infer_noexn p ctx t with
  | None ->
      let ids = Ctxt.names ctx in let term = term_in ids in
      fatal pos "%a is not typable." term t
  | Some (t, a) ->
      if Unif.solve_noexn p then
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

let check : Pos.popt -> problem -> ctxt -> term -> term -> term =
  fun pos p ctx t a ->
  let die () =
    let ids = Ctxt.names ctx in let term = term_in ids in
    fatal pos "[%a] does not have type [%a]." term t term a
  in
  match Infer.check_noexn p ctx t a with
  | Some t ->
    if Unif.solve_noexn p then
      begin
        if !p.unsolved = [] then t else
          (List.iter (wrn pos "Cannot solve %a." constr) !p.unsolved;
           die ())
      end
    else die ()
  | None -> die ()

let check_sort : Pos.popt -> problem -> ctxt -> term -> term * term =
  fun pos p ctx t ->
  match Infer.check_sort_noexn p ctx t with
  | None ->
      let ids = Ctxt.names ctx in let term = term_in ids in
      fatal pos "[%a] is not typable by a sort." term t
  | Some (t,s) ->
      if Unif.solve_noexn p then
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

(** [handle_query ss ps q] *)
let handle : Sig_state.t -> proof_state option -> p_query -> result =
  fun ss ps {elt;pos} ->
  match elt with
  | P_query_debug(_,"") ->
      let f (k,d) = Printf.sprintf "\n%c: %s" k d in
      let s = String.concat "" (List.map f (Logger.log_summary())) in
      return string ("debug flags:"^s)
  | P_query_debug(e,s) ->
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
  | P_query_flag("",_) ->
      let f n _ l = n::l in
      let l = Extra.StrMap.fold f Stdlib.(!Console.boolean_flags) [] in
      let l = List.sort Stdlib.compare l in
      let l = List.map (fun s -> "\""^s^"\"") l in
      return string ("flags: "^String.concat ", " l)
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
  | P_query_print(None) ->
      begin
        match ps with
        | None -> fatal pos "Not in a proof."
        | Some ps -> return Proof.goals ps
      end
  | P_query_print(Some qid) ->
      let sym_info ppf s =
        (* Function to print a definition. *)
        let def ppf = Option.iter (out ppf "@ ≔ %a" term) in
        (* Function to print a notation *)
        let notation ppf s =
          match !(s.sym_nota) with
          | NoNotation -> ()
          | n -> out ppf "notation %a %a;@." sym s (notation float) n
        in
        (* Function to print rules. *)
        let rules ppf s =
          match !(s.sym_rules) with
          | [] -> ()
          | r::rs ->
            let rule ppf r = sym_rule ppf (s,r) in
            let with_rule ppf r = out ppf "@.with %a" rule r in
            out ppf "rule %a%a;@." rule r (List.pp with_rule "") rs
        in
        (* Function to print a symbol declaration. *)
        let decl ppf s =
          out ppf "%a%a%asymbol %a : %a%a;@.%a%a"
            expo s.sym_expo prop s.sym_prop
            match_strat s.sym_mstrat sym s sym_type s
            def !(s.sym_def) notation s rules s
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
            List.pp decl "" ppf ind.ind_cons;
            decl ppf ind.ind_prop
          with Not_found -> ()
        in
        if s == Unif_rule.equiv || s == Coercion.coerce then rules ppf s
        else (decl ppf s; ind ppf s)
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
  | _ ->
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
  | P_query_search s ->
      let dbpath = Path.default_dbpath in
      return string (Tool.Indexing.search_cmd_txt ss s ~dbpath)
  | P_query_debug(_,_)
  | P_query_verbose(_)
  | P_query_flag(_,_)
  | P_query_prover(_)
  | P_query_prover_timeout(_)
  | P_query_print(_)
  | P_query_proofterm -> assert false (* already done *)
  | P_query_assert(must_fail, P_assert_typing(pt,pa)) ->
      let t = scope pt and a = scope ~typ:true pa in
      Console.out 2 "assertion: it is %b that %a" (not must_fail)
        typing (ctxt, t, a);
      (* Check that [a] is typable by a sort. *)
      let (a, _) = check_sort pos p ctxt a in
      let result =
        try ignore (check pos p ctxt t a); true
        with Fatal _ -> false
      in
      if result = must_fail then fatal pos "Assertion failed.";
      None
  | P_query_assert(must_fail, P_assert_conv(pt,pu)) ->
      let t = scope pt and u = scope pu in
      Console.out 2 "assertion: it is %b that %a" (not must_fail)
        constr (ctxt, t, u);
      (* Check that [t] is typable. *)
      let (t, a) = infer pt.pos p ctxt t in
      (* Check that [u] is typable. *)
      let (u, b) = infer pu.pos p ctxt u in
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
      let t = Eval.eval cfg ctxt (snd (infer pt.pos p ctxt t)) in
      let ids = Env.names (Proof.focus_env ps) in
      return (term_in ids) t
  | P_query_normalize(pt, cfg) ->
      let t = scope pt in
      let t = Eval.eval cfg ctxt (fst (infer pt.pos p ctxt t)) in
      let ids = Env.names (Proof.focus_env ps) in
      return (term_in ids) t
