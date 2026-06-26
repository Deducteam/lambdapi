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
  let xs = Array.init k (new_var_ind "x") in
  let ts = Array.map mk_Vari xs in
  (* We create the types for the “Mi” metavariables. *)
  let ty_m = Array.make (k+1) mk_Type in
  for i = 0 to k do
    for j = (i-1) downto 0 do
      ty_m.(i) <- mk_Prod (ty_m.(j), bind_var xs.(j) ty_m.(i))
    done
  done;
  (* We create the “Ai” terms and the “Mi” metavariables. *)
  let f i = mk_Meta (LibMeta.fresh p ty_m.(i) i, Array.sub ts 0 i) in
  let a = Array.init (k+1) f in
  (* We finally construct our type. *)
  let res = ref a.(k) in
  for i = k - 1 downto 0 do
    res := mk_Prod (a.(i), bind_var xs.(i) !res)
  done;
  !res

exception Meta_with_no_Patt of string

(** [symb_to_patt pos s2p names arities t] replaces in [t] every symbol [f]
    such that [SymMap.find f s2p = Some(_,i)] by [Patt(i,names.(i),_)]. *)
let symb_to_patt : Pos.popt -> (int * int option) SymMap.t -> string array
                   -> int array -> term -> term =
  fun pos s2p names arities ->
  let rec symb_to_patt t =
    let (h, ts) = get_args t in
    let ts = List.map symb_to_patt ts in
    let (h, ts) =
      match h with
      | Symb(f) ->
        begin match SymMap.find_opt f s2p with
          | Some(_,None) -> raise (Meta_with_no_Patt f.sym_name)
          | Some(_,Some i) ->
            let (ts1, ts2) = List.cut ts arities.(i) in
            (mk_Patt (Some i, names.(i), Array.of_list ts1), ts2)
          | None -> (mk_Symb f, ts)
        end
      | Vari(x)     -> (mk_Vari x, ts)
      | Type        -> (mk_Type  , ts)
      | Kind        -> (mk_Kind  , ts)
      | Abst(a,b)   ->
          let (x, t) = unbind b in
          let b = bind_var x (symb_to_patt t) in
          (mk_Abst (symb_to_patt a, b), ts)
      | Prod(a,b)   ->
          let (x, t) = unbind b in
          let b = bind_var x (symb_to_patt t) in
          (mk_Prod (symb_to_patt a, b), ts)
      | LLet(a,t,b) ->
          let (x, u) = unbind b in
          let b = bind_var x (symb_to_patt u) in
          (mk_LLet (symb_to_patt a, symb_to_patt t, b), ts)
      | Meta(_,_)   ->
          fatal pos "A metavariable could not be instantiated in the RHS."
      | Plac _      ->
        fatal pos "A placeholder hasn't been instantiated in the RHS."
      | Bvar _      -> assert false
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
  fun pos ((s,({lhs;names;rhs;arities;vars_nb;xvars_nb;_} as r)) as sr) ->
  (* Check that the variables of the RHS are in the LHS. *)
  assert (xvars_nb = 0);
  if Logger.log_enabled () then log_subj (Color.red "%a") sym_rule sr;
  (* Create a metavariable for each LHS pattern variable. *)
  LibMeta.reset_meta_counter();
  let p = new_problem() in
  let metas =
    Array.init vars_nb
      (fun i ->
         let arity = arities.(i) in
         (*FIXME: build_meta_type should take a sort as argument as some
            pattern variables are types and thus of sort KIND! *)
         let m = LibMeta.fresh p (build_meta_type p arity) arity in
         if Logger.log_enabled () then
           log_subj "pat $%d -> meta %a:%a" i meta m term !(m.meta_type);
         m)
  in
  (* Replace Patt's by Meta's of the same arity. *)
  let f m =
    let xs = Array.init m.meta_arity (new_var_ind "x") in
    let ts = Array.map mk_Vari xs in
    Some(bind_mvar xs (mk_Meta (m, ts)))
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
  if not (Unif.solve_noexn ~type_check:false p) then
    fatal pos "The LHS is not typable.";
  (* Try to simplify constraints. *)
  let norm_constr (c,t,u) =
    (c, Eval.snf [] (cleanup t), Eval.snf [] (cleanup u)) in
  let lhs_constrs =
    List.filter (fun (_,t,u) -> Term.cmp t u <> 0)
      (List.map norm_constr !p.unsolved) in
  if Logger.log_enabled () then
    log_subj "@[<v>LHS type: %a@ LHS constraints: %a@ rule: %a ↪ %a@]"
      term ty_lhs constrs lhs_constrs
      term lhs_with_metas term rhs_with_metas;
  (* Instantiate all uninstantiated metavariables by fresh symbols. *)
  (* Map each uninstantiated meta to a fresh symbol. *)
  let m2s = Stdlib.ref MetaMap.empty
  (* Map each new symbol to Some pattern index if any, and None otherwise. *)
  and s2p = Stdlib.ref SymMap.empty in
  let sym_of_meta m =
    let name = Printf.sprintf "%c%d" LibTerm.sym_meta_prefix m.meta_key in
    Term.create_sym (Sign.current_path())
      Privat Defin Eager false (Pos.none name) None !(m.meta_type) []
  in
  let instantiate m =
    match !(m.meta_value) with
    | Some _ -> assert false
    | None ->
      let s = sym_of_meta m in
      let xs = Array.init m.meta_arity (new_var_ind "x") in
      let t =
        Array.fold_left (fun t x -> mk_Appl(t,mk_Vari x)) (mk_Symb s) xs in
      m.meta_value := Some(bind_mvar xs t);
      if Logger.log_enabled() then
        log_subj "meta %a -> sym %s" meta m s.sym_name;
      Stdlib.(m2s := MetaMap.add m s !m2s);
      (* We record that this symbol needs to be eliminated. *)
      Stdlib.(s2p := SymMap.add s (m.meta_arity, None) !s2p)
  in
  MetaSet.iter instantiate !p.metas;
  (* Map s to Some i if metas.(i) is mapped to s. *)
  let f i m =
    match MetaMap.find_opt m Stdlib.(!m2s) with
    | Some s ->
      if Logger.log_enabled() then log_subj "sym %s -> pat ?%d" s.sym_name i;
      Stdlib.(s2p := SymMap.add s (m.meta_arity, Some i) !s2p)
    | None -> ()
  in
  Array.iteri f metas;
  (* If the meta associated to the pattern i is instantiated to another
     meta/symbol s mapped to no pattern, then we map s to i. *)
  let f i m =
    match !(m.meta_value) with
    | None -> ()
    | Some b ->
      let ts = Array.init m.meta_arity
          (fun i -> mk_Vari (new_var_ind "x" i)) in
      let t = msubst b ts in
      if Logger.log_enabled() then log_subj "%d: %a" i term t;
      match unfold t with
      | Symb s ->
        begin
          match Stdlib.(SymMap.find_opt s !s2p) with
          | Some (a, None) ->
            if a = m.meta_arity then
              begin
                if Logger.log_enabled() then
                  log_subj "sym %s -> pat $%d" s.sym_name i;
                Stdlib.(s2p := SymMap.add s (a, Some i) !s2p)
              end
            else wrn pos "%s of arity %d cannot be mapped to $%d of arity %d."
                s.sym_name a i m.meta_arity
          | _ -> ()
        end
      | _ -> ()
  in
  Array.iteri f metas;
  if Logger.log_enabled () then
    log_subj "replace LHS metavariables by function symbols:@ %a ↪ %a"
      term lhs_with_metas term rhs_with_metas;
  (* TODO complete the constraints into a set of rewriting rules on
     the function symbols of [symbols]. *)
  (* Compute the constraints for the RHS to have the same type as the LHS. *)
  let p = new_problem() in
  match Infer.check_noexn p [] rhs_with_metas ty_lhs with
  | None -> fatal pos "The RHS does not have the same type as the LHS."
  | Some rhs_with_metas ->
  if Logger.log_enabled () then
    log_subj "rule after inference of RHS type:@ %a ↪ %a"
      term lhs_with_metas term rhs_with_metas;
  (* Solving the typing constraints of the RHS. *)
  if not (Unif.solve_noexn p) then
    fatal pos "The rewriting rule does not preserve typing.";
  let rhs_constrs =
    List.filter (fun (_,t,u) -> Term.cmp t u <> 0)
      (List.map norm_constr !p.unsolved) in
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
  if Logger.log_enabled () then
    log_subj "rule after checking that the RHS has the same type:@ %a ↪ %a"
      term lhs_with_metas term rhs_with_metas;
  if cs <> [] then
    begin
      List.iter (fatal_msg "Cannot solve %a.@." constr) cs;
      fatal pos "Unable to prove type preservation."
    end;
  (* Replace metavariable symbols by patterns. *)
  try
    let rhs = symb_to_patt pos Stdlib.(!s2p) names arities rhs_with_metas in
    s, {r with rhs}
  with Meta_with_no_Patt n ->
    fatal pos
      "Cannot prove that@.%a@.preserves typing. The rule obtained after \
       typing is:@.%a ↪ %a@.But %s cannot be deduced from the declared \
       pattern variables.@.Some pattern variable possibly needs to be \
       explicited." sym_rule sr term lhs_with_metas term rhs_with_metas n

let check_rule p r = print_implicits_and_domains_in (check_rule p) r
