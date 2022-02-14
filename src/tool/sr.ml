(** Checking that a rule preserves typing (subject reduction property). *)

open Lplib
open Timed
open Common open Error
open Core open Term open Print

(** Logging function for typing. *)
let log_subj = Logger.make 's' "subj" "subject-reduction"
let log_subj = log_subj.pp

(** [build_meta_type p k] builds the type “Πx1:A1,⋯,xk:Ak,A(k+1)” where the
   type “Ai = Mi[x1,⋯,x(i-1)]” is defined as the metavariable “Mi” which has
   arity “i-1” and type “Π(x1:A1) ⋯ (x(i-1):A(i-1)), TYPE”, and adds the
   metavariables in [p]. *)
let build_meta_type : problem -> int -> term = fun p k ->
  assert (k >= 0);
  let xs = Array.init k (new_tvar_ind "x") in
  let ts = Array.map mk_Vari xs in
  (* We create the types for the “Mi” metavariables. *)
  let ty_m = Array.make (k+1) mk_Type in
  for i = 0 to k do
    for j = (i-1) downto 0 do
      ty_m.(i) <- mk_Prod (ty_m.(j), Bindlib.bind_var xs.(j) ty_m.(i))
    done
  done;
  (* We create the “Ai” terms and the “Mi” metavariables. *)
  let f i = mk_Meta (LibMeta.fresh p ty_m.(i) i, Array.sub ts 0 i) in
  let a = Array.init (k+1) f in
  (* We finally construct our type. *)
  let res = ref a.(k) in
  for i = k - 1 downto 0 do
    res := mk_Prod (a.(i), Bindlib.bind_var xs.(i) !res)
  done;
  !res

(** [symb_to_patt pos map t] replaces in [t] every symbol [f] such that
   [SymMap.find f map = Some i] by [Patt(i,_,_)]. *)
let symb_to_patt : Pos.popt -> (int * int) option SymMap.t -> term -> term =
  fun pos map ->
  let rec symb_to_patt t =
    let (h, ts) = get_args t in
    let ts = List.map symb_to_patt ts in
    let (h, ts) =
      match h with
      | Symb(f) ->
        begin match SymMap.find_opt f map with
          | Some None ->
            (* A symbol may also come from a metavariable that appeared in the
               type of a metavariable that was replaced by a symbol. We do not
               have concrete examples of that happening yet. *)
            fatal pos "Introduced symbol [%s] cannot be removed." f.sym_name
          | Some (Some (i, arity)) ->
            let (ts1, ts2) = List.cut ts arity in
            (mk_Patt (Some i, string_of_int i, Array.of_list ts1), ts2)
          | None -> (mk_Symb f, ts)
        end
      | Vari(x)     -> (mk_Vari x, ts)
      | Type        -> (mk_Type  , ts)
      | Kind        -> (mk_Kind  , ts)
      | Abst(a,b)   ->
          let (x, t) = Bindlib.unbind b in
          let b = Bindlib.bind_var x (symb_to_patt t) in
          (mk_Abst (symb_to_patt a, b), ts)
      | Prod(a,b)   ->
          let (x, t) = Bindlib.unbind b in
          let b = Bindlib.bind_var x (symb_to_patt t) in
          (mk_Prod (symb_to_patt a, b), ts)
      | LLet(a,t,b) ->
          let (x, u) = Bindlib.unbind b in
          let b = Bindlib.bind_var x (symb_to_patt u) in
          (mk_LLet (symb_to_patt a, symb_to_patt t, b), ts)
      | Meta(_,_)   ->
          fatal pos "A metavariable could not be instantiated in the RHS."
      | Plac _      ->
        fatal pos "A placeholder hasn't been instantiated in the RHS."
      | Db _ -> assert false
      | Appl(_,_)   -> assert false (* Cannot appear in RHS. *)
      | Patt(_,_,_) -> assert false (* Cannot appear in RHS. *)
      | Wild        -> assert false (* Cannot appear in RHS. *)
      | TRef(_)     -> assert false (* Cannot appear in RHS. *)
    in
    add_args h ts
  in
  symb_to_patt

(** [check_rule r] checks whether the rule [r] preserves typing. *)
let check_rule : Pos.popt -> sym_rule -> sym_rule =
  fun pos ((s, ({lhs; rhs; arities; vars_nb; xvars_nb; _} as r)) as sr) ->
  (* Check that the variables of the RHS are in the LHS. *)
  assert (xvars_nb = 0);
  if Logger.log_enabled () then log_subj (Color.red "%a") sym_rule sr;
  (* Create a metavariable for each LHS pattern variable. *)
  let p = new_problem() in
  let metas =
    Array.init vars_nb
      (fun i ->
         let arity = arities.(i) in
         (*FIXME: build_meta_type should take a sort as argument as some
            pattern variables are types and thus of sort KIND! *)
         LibMeta.fresh p (build_meta_type p arity) arity)
  in
  (* Replace Patt's by Meta's. *)
  let f m =
    let xs = Array.init m.meta_arity (new_tvar_ind "x") in
    let ts = Array.map mk_Vari xs in
    Some(Bindlib.bind_mvar xs (mk_Meta (m, ts)))
  in
  let su = Array.map f metas in
  let lhs_with_metas = subst_patt su (add_args (mk_Symb s) lhs)
  and rhs_with_metas = subst_patt su rhs in
  if Logger.log_enabled () then
    log_subj "replace pattern variables by metavariables:@ %a ↪ %a"
      term lhs_with_metas term rhs_with_metas;
  (* Infer the typing constraints of the LHS. *)
  match Infer.infer_noexn p [] lhs_with_metas with
  | None -> fatal pos "The LHS is not typable."
  | Some (lhs_with_metas, ty_lhs) ->
  (* Try to simplify constraints. *)
  if not (Unif.solve_noexn ~type_check:false p) then
    fatal pos "The LHS is not typable.";
  let norm_constr (c,t,u) = (c, Eval.snf [] t, Eval.snf [] u) in
  let lhs_constrs = List.map norm_constr !p.unsolved in
  if Logger.log_enabled () then
    log_subj "@[<v>LHS type: %a@ LHS constraints: %a@ rule: %a ↪ %a@]"
      term ty_lhs constrs lhs_constrs
      term lhs_with_metas term rhs_with_metas;
  (* Instantiate all uninstantiated metavariables by fresh symbols. *)
  (*let symbols =
    let symbols = Stdlib.ref SymSet.empty in
    let rec instantiate i m =
      match !(m.meta_value) with
      | Some _ ->
        (* Instantiate recursively the meta-variables of the definition. *)
        let t = mk_Meta(m, Array.make m.meta_arity mk_Kind) in
        LibMeta.iter true (instantiate None) [] t
      | None ->
        (* Instantiate recursively the meta-variables of the type. *)
        LibMeta.iter true (instantiate None) [] !(m.meta_type);
        (* Create a new symbol. *)
        let s =
          let name = Pos.none @@ Printf.sprintf "$%d" m.meta_key in
          Term.create_sym (Sign.current_path()) Privat Defin Eager
            false name !(m.meta_type) [] in
        Stdlib.(symbols := SymSet.add s !symbols);
        (* Build a definition for [m]. *)
        let xs = Array.init m.meta_arity (new_tvar_ind "x") in
        let s = mk_Symb s in
        let def = Array.fold_left (fun t x -> _Appl t (mk_Vari x)) s xs in
        m.meta_value := Some(Bindlib.bind_mvar xs def)
    in
    Array.iter instantiate metas;
    Stdlib.(!symbols)
  in*)
  let map = Stdlib.ref SymMap.empty
  and m2s = Stdlib.ref MetaMap.empty in
  let instantiate m =
    match !(m.meta_value) with
    | Some _ -> assert false
    | None ->
      let s =
        let name = Pos.none @@ Printf.sprintf "$%d" m.meta_key in
        Term.create_sym (Sign.current_path())
          Privat Defin Eager false name !(m.meta_type) []
      in
      Stdlib.(map := SymMap.add s None !map; m2s := MetaMap.add m s !m2s);
      let xs = Array.init m.meta_arity (new_tvar_ind "x") in
      let s = mk_Symb s in
      let def = Array.fold_left (fun t x -> mk_Appl (t, mk_Vari x)) s xs in
      m.meta_value := Some(Bindlib.bind_mvar xs def)
  in
  MetaSet.iter instantiate !p.metas;
  let f i m =
    match MetaMap.find_opt m Stdlib.(!m2s) with
    | Some s -> Stdlib.(map := SymMap.add s (Some (i, arities.(i))) !map)
    | None -> ()
  in
  Array.iteri f metas;
  if Logger.log_enabled () then
    log_subj "replace LHS metavariables by function symbols:@ %a ↪ %a"
      term lhs_with_metas term rhs_with_metas;
  (* TODO complete the constraints into a set of rewriting rules. *)
  (* Compute the constraints for the RHS to have the same type as the LHS. *)
  let p = new_problem() in
  match Infer.check_noexn p [] rhs_with_metas ty_lhs with
  | None -> fatal pos "The RHS does not have the same type as the LHS."
  | Some rhs_with_metas ->
  (* Solving the typing constraints of the RHS. *)
  if not (Unif.solve_noexn p) then
    fatal pos "The rewriting rule does not preserve typing.";
  let rhs_constrs = List.map norm_constr !p.unsolved in
  (* [matches p t] says if [t] is an instance of [p]. *)
  let matches p t =
    let rec matches s l =
      match l with
      | [] -> ()
      | (p,t)::l ->
        (*if Logger.log_enabled() then
          log_subj "matches [%a] [%a]" term p term t;*)
        match unfold p, unfold t with
        | Vari x, _ ->
          begin match VarMap.find_opt x s with
            | Some u ->
              if Eval.eq_modulo [] t u then matches s l else raise Exit
            | None -> matches (VarMap.add x t s) l
          end
        | Symb f, Symb g when f == g -> matches s l
        | Appl(t1,u1), Appl(t2,u2) -> matches s ((t1,t2)::(u1,u2)::l)
        | _ -> raise Exit
    in try matches VarMap.empty [p,t]; true with Exit -> false
  in
  (* Function saying if a constraint is an instance of another one. *)
  let is_inst ((_c1,t1,u1) as x1) ((_c2,t2,u2) as x2) =
    if Logger.log_enabled() then
      log_subj "is_inst [%a] [%a]" constr x1 constr x2;
    let cons t u = add_args (mk_Symb Unif_rule.equiv) [t; u] in
    matches (cons t1 u1) (cons t2 u2) || matches (cons t1 u1) (cons u2 t2)
  in
  let is_lhs_constr rc = List.exists (fun lc -> is_inst lc rc) lhs_constrs in
  let cs = List.filter (fun rc -> not (is_lhs_constr rc)) rhs_constrs in
  if cs <> [] then
    begin
      List.iter (fatal_msg "Cannot solve %a@." constr) cs;
      fatal pos "Unable to prove type preservation."
    end;
  (* Replace metavariable symbols by Patt's. *)
  let rhs = symb_to_patt pos Stdlib.(!map) rhs_with_metas in
  s, {r with rhs}
