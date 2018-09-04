(** Scoping. *)

open Console
open Extra
open Files
open Pos
open Parser
open Terms
open Env

(** [find_ident env qid] returns a boxed term corresponding to a  variable  of
    the environment [env] (or to a symbol) which name corresponds to [qid]. In
    the case where the module path [fst qid.elt] is empty, we first search for
    the name [snd qid.elt] in the environment, and if it is not mapped we also
    search in the current signature. The exception [Fatal] is raised on errors
    (i.e., when the name cannot be found, or the module path is invalid). *)
let find_ident : env -> qident -> tbox = fun env qid ->
  let {elt = (mp, s); pos} = qid in
  if mp = [] then
    (* No module path, search the local environment first. *)
    try _Vari (Env.find s env) with Not_found ->
    (* Then, search in the global environment. *)
    try _Symb (Sign.find (Sign.current_sign()) s) with Not_found ->
    fatal pos "Unbound variable or symbol [%s]." s
  else
    let sign = Sign.current_sign() in
    if not Sign.(mp = sign.path || PathMap.mem mp Timed.(!(sign.deps))) then
      (* Module path is not available (not loaded), fail. *)
      fatal pos "No module [%a] loaded." Files.pp_path mp
    else
      (* Module path loaded, look for symbol. *)
      let sign =
        try PathMap.find mp Timed.(!Sign.loaded)
        with _ -> assert false (* cannot fail. *)
      in
      try _Symb (Sign.find sign s) with Not_found ->
      fatal pos "Unbound symbol [%a.%s]." Files.pp_path mp s

(** [scope_term mmap env t] turns a parser-level term [t] into an actual term.
    Note that this term may use the variables of the environment [env] as well
    as metavariables mapped in [mmap]. Note that wildcards (i.e., terms of the
    form [P_Wild]) are transformed into fresh metavariables.  When not type is
    given for the domains of an abstraction or a product a fresh metavariables
    is also introduced. Mtavariable names are looked up in [mmap] first, and a
    fresh term metavariable is created if the name is not mapped. Note that if
    such fresh name is used twice, the same metavariable is referenced. *)
let scope_term : meta StrMap.t -> env -> p_term -> term = fun mmap env t ->
  let mmap = Pervasives.ref mmap in
  let rec scope : env -> p_term -> tbox = fun env t ->
    match t.elt with
    | P_Vari(qid)   -> find_ident env qid
    | P_Type        -> _Type
    | P_Prod(x,a,b) ->
        let v = Bindlib.new_var mkfree x.elt in
        let a = scope_domain env a in
        _Prod a (Bindlib.bind_var v (scope (Env.add x.elt v a env) b))
    | P_Abst(x,a,t) ->
        let v = Bindlib.new_var mkfree x.elt in
        let a = scope_domain env a in
        _Abst a (Bindlib.bind_var v (scope (Env.add x.elt v a env) t))
    | P_Appl(t,u)   -> _Appl (scope env t) (scope env u)
    | P_Wild        ->
        (* We build a metavariable that may use the variables of [env]. *)
        let vs = Env.vars_of_env env in
        let a =
          let m = fresh_meta (prod_of_env env _Type) (Array.length vs) in
          prod_of_env env (_Meta m vs)
        in
        _Meta (fresh_meta a (List.length env)) vs
    | P_Meta(id,ts) ->
        let m =
          (* We first check if the metavariable is in the map. *)
          try StrMap.find id.elt !mmap with Not_found ->
          (* Otherwise we create a new metavariable. *)
          let a =
            let vs = Env.vars_of_env env in
            let m = fresh_meta (prod_of_env env _Type) (Array.length vs) in
            prod_of_env env (_Meta m vs)
          in
          let m = fresh_meta ~name:id.elt a (List.length env) in
          mmap := StrMap.add id.elt m !mmap; m
        in
        (* The environment of the metavariable is build from [ts]. *)
        _Meta m (Array.map (scope env) ts)
  and scope_domain : env -> p_term option -> tbox = fun env t ->
    match t with
    | Some(t) -> scope env t
    | None    ->
        (* We build a metavariable that may use the variables of [env]. *)
        let a = prod_of_env env _Type in
        let vs = Env.vars_of_env env in
        _Meta (fresh_meta a (Array.length vs)) vs
  in
  Bindlib.unbox (scope env t)

(** Association list giving an environment index to “pattern variable”. *)
type pattern_map = (string * int) list

(** Representation of a LHS (pattern) as a head symbol and its arguments. *)
type full_lhs = sym * term list

(** [scope_lhs map t] computes a rule LHS from the parser-level term [t].  The
    association list [map] gives the index that is reserved in the environment
    for “pattern variables”.  Only the variables that are bound in the RHS (or
    appear non-linearly in the LHS) have an associated index in [map]. *)
let scope_lhs : pattern_map -> p_term -> full_lhs = fun map t ->
  let fresh =
    let c = Pervasives.ref (-1) in
    fun () -> incr c; Printf.sprintf "#%i" !c
  in
  let rec scope : env -> p_term -> tbox = fun env t ->
    match t.elt with
    | P_Vari(qid)   -> find_ident env qid
    | P_Type        -> fatal t.pos "Invalid LHS (sort [Type])."
    | P_Prod(_,_,_) -> fatal t.pos "Invalid LHS (product type)."
    | P_Abst(x,a,t) ->
        let v = Bindlib.new_var mkfree x.elt in
        let a =
          match a with
          | Some(a) -> fatal a.pos "Invalid LHS (type annotation)."
          | None    -> scope env (Pos.none P_Wild)
        in
        _Abst a (Bindlib.bind_var v (scope (Env.add x.elt v a env) t))
    | P_Appl(t,u)   -> _Appl (scope env t) (scope env u)
    | P_Wild        ->
        let e = List.map (fun (_,(x,_)) -> _Vari x) env in
        let m = fresh () in
        _Patt None m (Array.of_list e)
    | P_Meta(id,ts) ->
        let e = Array.map (scope env) ts in
        let i = try Some(List.assoc id.elt map) with Not_found -> None in
        _Patt i id.elt e
  in
  let (h, args) = get_args (Bindlib.unbox (scope [] t)) in
  match h with
  | Symb(s) when s.sym_const -> fatal t.pos "LHS with a static head symbol."
  | Symb(s)                  -> (s, args)
  | _                        -> fatal t.pos "LHS with no head symbol."

(* NOTE wildcards are given a unique name so that we can produce more readable
   error messages. The names are formed of a number prefixed by ['#']. *)

(** Representation of the RHS of a rule. *)
type rhs = (term_env, term) Bindlib.mbinder

(** [scope_rhs map t] computes a rule RHS from the parser-level term [t].  The
    association list [map] gives the position of every  “pattern variable”  in
    the constructed multiple binder. *)
let scope_rhs : pattern_map -> p_term -> rhs = fun map t ->
  let names =
    let sorted_map = List.sort (fun (_,i) (_,j) -> i - j) map in
    Array.of_list (List.map fst sorted_map)
  in
  let metas = Bindlib.new_mvar (fun m -> TE_Vari(m)) names in
  let rec scope : env -> p_term -> tbox = fun env t ->
    match t.elt with
    | P_Vari(qid)   -> find_ident env qid
    | P_Type        -> _Type
    | P_Prod(x,a,b) ->
        let v = Bindlib.new_var mkfree x.elt in
        let a = scope_domain env t.pos a in
        _Prod a (Bindlib.bind_var v (scope (Env.add x.elt v a env) b))
    | P_Abst(x,a,t) ->
        let v = Bindlib.new_var mkfree x.elt in
        let a = scope_domain env t.pos a in
        _Abst a (Bindlib.bind_var v (scope (Env.add x.elt v a env) t))
    | P_Appl(t,u)   -> _Appl (scope env t) (scope env u)
    | P_Wild        -> fatal t.pos "Invalid RHS (wildcard).\n"
    | P_Meta(m,e)   ->
        let e = Array.map (scope env) e in
        let i =
          try List.assoc m.elt map with Not_found ->
            fatal m.pos "Unbound pattern variable [%s]." m.elt
        in
        _TEnv (Bindlib.box_var metas.(i)) e
  and scope_domain : env -> popt -> p_term option -> tbox = fun env p t ->
    match t with
    | Some(t) -> scope env t
    | None    -> fatal p "Missing type annotation."
  in
  Bindlib.unbox (Bindlib.bind_mvar metas (scope [] t))

(** [meta_vars t] returns a couple [(mvs,nl)]. The first compoment [mvs] is an
    association list giving the arity of all the “pattern variables” appearing
    in the parser-level term [t]. The second component [nl] contains the names
    of the “pattern variables” that appear non-linearly.  If a given  “pattern
    variable” occurs with different arities the program fails gracefully. *)
let meta_vars : p_term -> (string * int) list * string list = fun t ->
  let rec meta_vars acc t =
    match t.elt with
    | P_Vari(_)
    | P_Type
    | P_Wild              -> acc
    | P_Prod(_,None,b)
    | P_Abst(_,None,b)    -> meta_vars acc b
    | P_Prod(_,Some(a),b)
    | P_Abst(_,Some(a),b)
    | P_Appl(a,b)         -> meta_vars (meta_vars acc a) b
    | P_Meta(m,e)         ->
        let ((ar,nl) as acc) = Array.fold_left meta_vars acc e in
        let l = Array.length e in
        begin
          try
            if List.assoc m.elt ar <> l then
              fatal m.pos "Arity mismatch for metavariable [%s]." m.elt;
            if List.mem m.elt nl then acc else (ar, m.elt::nl)
          with Not_found -> ((m.elt,l)::ar, nl)
        end
  in meta_vars ([],[]) t

(** [scope_rule r] turns the parser-level rewriting rule [r] into a  rewriting
    rule (and the associated head symbol). *)
let scope_rule : p_rule -> sym * rule = fun (p_lhs, p_rhs) ->
  (* Compute the set of the meta-variables on both sides. *)
  let (mvs_lhs, nl) = meta_vars p_lhs in
  let (mvs    , _ ) = meta_vars p_rhs in
  (* NOTE to reject non-left-linear rules, we can check [nl = []] here. *)
  (* Check that the meta-variables of the RHS exist in the LHS. *)
  let check_in_lhs (m,i) =
    let j =
      try List.assoc m mvs_lhs with Not_found ->
      fatal p_rhs.pos "Unknown pattern variable [%s]." m
    in
    if i <> j then fatal p_lhs.pos "Arity mismatch for [%s]." m
  in
  List.iter check_in_lhs mvs;
  let mvs = List.map fst mvs in
  (* Reserve space for meta-variables that appear non-linearly in the LHS. *)
  let nl = List.filter (fun m -> not (List.mem m mvs)) nl in
  let mvs = List.mapi (fun i m -> (m,i)) (mvs @ nl) in
  (* NOTE [mvs] maps meta-variables to their position in the environment. *)
  (* NOTE meta-variables not in [mvs] can be considered as wildcards. *)
  (* We scope the LHS and add indexes in the enviroment for meta-variables. *)
  let (sym, lhs) = scope_lhs mvs p_lhs in
  (* We scope the RHS and bind the meta-variables. *)
  let rhs = scope_rhs mvs p_rhs in
  (* We put everything together to build the rule. *)
  (sym, {lhs; rhs; arity = List.length lhs})

(** [translate_old_rule r] transforms the legacy representation of a rule into
    the new representation. This function will be removed soon. *)
let translate_old_rule : old_p_rule -> p_rule = fun (ctx,lhs,rhs) ->
  let get_var ({elt},ao) =
    let fn a =
      if Timed.(!verbose) > 1 then
        wrn "Ignored type annotation at [%a].\n" Pos.print a.pos
    in
    Option.iter fn ao; elt
  in
  let ctx = List.map get_var ctx in
  let is_pat_var env x = not (List.mem x env) && List.mem x ctx in
  let arity = Hashtbl.create 7 in

  (** Find the minimum number of arguments a variable is applied to. *)
  let rec compute_arities env t =
    let h, lts = Parser.get_args t in
    match h.elt with
    | P_Vari({elt = ([],x)}) when is_pat_var env x ->
       begin
         let m = List.length lts in
         try
           let n = Hashtbl.find arity x in
           if m < n then Hashtbl.replace arity x m
         with Not_found ->
           Hashtbl.add arity x m
       end
    | _ ->
       match t.elt with
       | P_Vari(_)
       | P_Wild
       | P_Type
       | P_Prod(_,_,_)
       | P_Meta(_,_)   -> ()
       | P_Abst(x,_,u) -> compute_arities (x.elt::env) u
       | P_Appl(t1,t2) -> compute_arities env t1; compute_arities env t2
  in

  let rec build env t =
    let h, lts = Parser.get_args t in
    match h.elt with
    | P_Vari({elt = ([],x)}) when is_pat_var env x ->
       let lts = List.map (fun (p,t) -> p,build env t) lts in
       begin
         try
           let n = Hashtbl.find arity x in
           let lts1, lts2 = List.cut lts n in
           let ts1 = List.map snd lts1 in
           let h = Pos.make t.pos (P_Meta(Pos.none x, Array.of_list ts1)) in
           Parser.add_args h lts2
         with Not_found ->
           assert false
       end
    | _ ->
       match t.elt with
       | P_Vari(_)
       | P_Type
       | P_Wild -> t
       | P_Prod(_,None,_) -> assert false
       | P_Prod(x,Some(a),b) ->
          let a = build env a in
          let b = build (x.elt::env) b in
          Pos.make t.pos (P_Prod(x,Some(a),b))
       | P_Abst(x,a,u) ->
          let a = match a with Some(a) -> Some(build env a) | _ -> None in
          let u = build (x.elt::env) u in
          Pos.make t.pos (P_Abst(x,a,u))
       | P_Appl(t1,t2) ->
          let t1 = build env t1 in
          let t2 = build env t2 in
          Pos.make t.pos (P_Appl(t1,t2))
       | P_Meta(_,_)   ->
          fatal t.pos "Invalid legacy rule syntax."
  in
  (* NOTE the computation order is important for setting arities properly. *)
  compute_arities [] lhs;
  let lhs = build [] lhs in
  let rhs = build [] rhs in
  (lhs, rhs)

(** [scope_rw_spec mmap env t] turns a parser-level rewrite specification  [s]
    into an actual rewrite specification. It may use the variables of [env] as
    well as metavariables mapped in [mmap]. *)
let scope_rw_patt : meta StrMap.t -> env -> p_rw_patt loc
                    -> Rewrite.rw_patt = fun m env s ->
  let open Rewrite in
  match s.elt with
  | P_Term(t)               -> RW_Term(scope_term m env t)
  | P_InTerm(t)             -> RW_InTerm(scope_term m env t)
  | P_InIdInTerm(x,t)       ->
      let v = Bindlib.new_var mkfree x.elt in
      let t = scope_term m ((x.elt,(v, _Kind))::env) t in
      RW_InIdInTerm(Bindlib.unbox (Bindlib.bind_var v (lift t)))
  | P_IdInTerm(x,t)         ->
      let v = Bindlib.new_var mkfree x.elt in
      let t = scope_term m ((x.elt,(v, _Kind))::env) t in
      RW_IdInTerm(Bindlib.unbox (Bindlib.bind_var v (lift t)))
  | P_TermInIdInTerm(u,x,t) ->
      let u = scope_term m env u in
      let v = Bindlib.new_var mkfree x.elt in
      let t = scope_term m ((x.elt,(v, _Kind))::env) t in
      RW_TermInIdInTerm(u, Bindlib.unbox (Bindlib.bind_var v (lift t)))
  | P_TermAsIdInTerm(u,x,t) ->
      let u = scope_term m env u in
      let v = Bindlib.new_var mkfree x.elt in
      let t = scope_term m ((x.elt,(v, _Kind))::env) t in
      RW_TermAsIdInTerm(u, Bindlib.unbox (Bindlib.bind_var v (lift t)))
