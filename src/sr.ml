(** Type-checking and inference. *)

open Timed
open Console
open Terms
open Print
open Extra

(** Logging function for typing. *)
let log_subj =
  new_logger 'j' "subj" "debugging information for subject-reduction"
let log_subj = log_subj.logger

(** Representation of a substitution. *)
type subst = tvar array * term array

(** [subst_from_constrs cs] builds a //typing substitution// from the list  of
    constraints [cs]. The returned substitution is given by a couple of arrays
    [(xs,ts)] of the same length.  The array [xs] contains the variables to be
    substituted using the terms of [ts] at the same index. *)
let subst_from_constrs : (term * term) list -> subst = fun cs ->
  let rec build_sub acc cs =
    match cs with
    | []        -> List.split acc
    | (a,b)::cs ->
    let (ha,argsa) = Basics.get_args a in
    let (hb,argsb) = Basics.get_args b in
    let na = List.length argsa in
    let nb = List.length argsb in
    match (unfold ha, unfold hb) with
    | (Symb(sa,_), Symb(sb,_)) when sa == sb && na = nb && Sign.is_inj sa ->
        let fn l t1 t2 = (t1,t2) :: l in
        build_sub acc (List.fold_left2 fn cs argsa argsb)
    | (Vari(x)   , _         ) when argsa = [] -> build_sub ((x,b)::acc) cs
    | (_         , Vari(x)   ) when argsb = [] -> build_sub ((x,a)::acc) cs
    | (_         , _         )                 -> build_sub acc cs
  in
  let (vs,ts) = build_sub [] cs in
  (Array.of_list vs, Array.of_list ts)

(* Does not work in examples/cic.dk

let build_meta_type : int -> term = fun k ->
  let m' = new_meta Type (*FIXME?*) k in
  let m_typ = Meta(m',[||]) in
  let m = new_meta m_typ k in
  Meta(m,[||])
*)

(** [build_meta_type k] builds the type “∀(x₁:A₁) (x₂:A₂) ⋯ (xk:Ak), B” where
    “x₁” through “xk” are fresh variables, “Ai = Mi[x₁,⋯,x(i-1)]”, “Mi” is a
    new metavar of arity “i-1” and type “∀(x₁:A₂) ⋯ (x(i-1):A(i-1), TYPE”. *)
let build_meta_type : int -> term = fun k ->
  assert (k>=0);
  let vs = Bindlib.new_mvar mkfree (Array.make k "x") in
  let rec build_prod k p =
    if k = 0 then p
    else
      let k = k-1 in
      let mk_typ = Bindlib.unbox (build_prod k _Type) in
      let mk = fresh_meta mk_typ k in
      let tk = _Meta mk (Array.map _Vari (Array.sub vs 0 k)) in
      let b = Bindlib.bind_var vs.(k) p in
      let p = Bindlib.box_apply2 (fun a b -> Prod(a,b)) tk b in
      build_prod k p
  in
  let mk_typ = Bindlib.unbox (build_prod k _Type) (*FIXME?*) in
  let mk = fresh_meta mk_typ k in
  let tk = _Meta mk (Array.map _Vari vs) in
  Bindlib.unbox (build_prod k tk)

(** Translation from Xml-light
    (https://opam.ocaml.org/packages/xml-light/xml-light.2.4/) to Lambdapi **)

(** [find_trs xml] finds the Xml node corresponding to the TRS in an Xml node
    obtained from a CPF file. In a valid CPF file generated from external
    tools for the Knuth-Bendix completion, there is exactly one such node. **)
let find_trs : Xml.xml -> Xml.xml = fun xml ->
  let rec find_tag : string -> Xml.xml -> Xml.xml option = fun s xml ->
    if Xml.tag xml = s then Some xml
    else
      let rec iter f = function
        | []      -> None
        | x :: xs -> match f x with
            | None -> iter f xs
            | y    -> y in
      iter (find_tag s) (Xml.children xml)
  in
  match find_tag "completionInput" xml with
  | None      -> assert false
  | Some xml  ->
      match find_tag "trs" xml with
      | None     -> assert false
      | Some xml -> xml

(** [get_only_child xml] returns the only child of an Xml node given **)
let get_only_child : Xml.xml -> Xml.xml = fun xml ->
  match Xml.children xml with
  | [xml] -> xml
  | _     -> assert false

(** [get_term sign xml] translates an Xml node of tag name "var" or "funapp"
    into a term according to the signature state of the original system **)
let rec get_term : Sign.t -> Xml.xml -> term = fun sign xml ->
  match Xml.tag xml with
  | "var"    -> (* to finish *) assert false
  | "funapp" -> begin match Xml.children xml with
      | []        -> assert false
      | f :: args ->
          match get_only_child f with
          | Xml.Element _ -> assert false
          | Xml.PCData str  ->
              let args = List.map get_arg args in
              let s, path =
                match String.split_on_char '_' str with
                | ["c"; path; s] ->
                    s, String.split_on_char '.' path
                | _ -> assert false in
              let sign = PathMap.find path Sign.(!loaded) in
              let sym =
                try symb (Sign.find sign s) with Not_found -> assert false in
              List.fold_left (fun u v -> Appl (u, v)) s args
      end
  | _             -> assert false

(** [get_arg xml] translates an Xml node of tag name "arg" into a term **)
and get_arg : Xml.xml -> term = fun xml -> get_term (get_only_child xml)


(** [check_rule builtins r] check whether rule [r] is well-typed. The program
    fails gracefully in case of error. *)
let check_rule : sym StrMap.t -> sym * pp_hint * rule Pos.loc -> unit
  = fun builtins (s,h,r) ->
  if !log_enabled then log_subj "check_rule [%a]" pp_rule (s, h, r.elt);
  (* We process the LHS to replace pattern variables by metavariables. *)
  let arity = Bindlib.mbinder_arity r.elt.rhs in
  let metas = Array.init arity (fun _ -> None) in
  let rec to_m : int -> term -> tbox = fun k t ->
    match unfold t with
    | Vari(x)     -> _Vari x
    | Symb(s,h)   -> _Symb s h
    | Abst(a,t)   -> let (x,t) = Bindlib.unbind t in
                     _Abst (to_m 0 a) (Bindlib.bind_var x (to_m 0 t))
    | Appl(t,u)   -> _Appl (to_m (k+1) t) (to_m 0 u)
    | Patt(i,n,a) ->
        begin
          let a = Array.map (to_m 0) a in
          let l = Array.length a in
          match i with
          | None    ->
             let m = fresh_meta ~name:n (build_meta_type (l+k)) l in
             _Meta m a
          | Some(i) ->
              match metas.(i) with
              | Some(m) -> _Meta m a
              | None    ->
                 let m = fresh_meta ~name:n (build_meta_type (l+k)) l in
                 metas.(i) <- Some(m);
                 _Meta m a
        end
    | Type        -> assert false (* Cannot appear in LHS. *)
    | Kind        -> assert false (* Cannot appear in LHS. *)
    | Prod(_,_)   -> assert false (* Cannot appear in LHS. *)
    | Meta(_,_)   -> assert false (* Cannot appear in LHS. *)
    | TEnv(_,_)   -> assert false (* Cannot appear in LHS. *)
    | Wild        -> assert false (* Cannot appear in LHS. *)
    | TRef(_)     -> assert false (* Cannot appear in LHS. *)
  in
  let lhs = List.map (fun p -> Bindlib.unbox (to_m 0 p)) r.elt.lhs in
  let lhs = Basics.add_args (Symb(s,h)) lhs in
  (* We substitute the RHS with the corresponding metavariables.*)
  let fn m =
    let m = match m with Some(m) -> m | None -> assert false in
    let xs = Array.init m.meta_arity (Printf.sprintf "x%i") in
    let xs = Bindlib.new_mvar mkfree xs in
    let e = Array.map _Vari xs in
    TE_Some(Bindlib.unbox (Bindlib.bind_mvar xs (_Meta m e)))
  in
  let te_envs = Array.map fn metas in
  let rhs = Bindlib.msubst r.elt.rhs te_envs in
  (* Infer the type of the LHS and the constraints. *)
  match Typing.infer_constr builtins Ctxt.empty lhs with
  | None                      -> wrn r.pos "Untypable LHS."
  | Some(lhs_constrs, ty_lhs) ->
  if !log_enabled then
    begin
      log_subj "LHS has type [%a]" pp ty_lhs;
      let fn (t,u) = log_subj "  if [%a] ~ [%a]" pp t pp u in
      List.iter fn lhs_constrs
    end;
  (* Turn constraints into a substitution and apply it. *)
  let (xs,ts) = subst_from_constrs lhs_constrs in
  let p = Bindlib.box_pair (lift rhs) (lift ty_lhs) in
  let p = Bindlib.unbox (Bindlib.bind_mvar xs p) in
  let (rhs,ty_lhs) = Bindlib.msubst p ts in
  (* Check that the RHS has the same type as the LHS. *)
  let to_solve = Infer.check Ctxt.empty rhs ty_lhs in
  if !log_enabled && to_solve <> [] then
    begin
      log_subj "RHS has type [%a]" pp ty_lhs;
      let fn (t,u) = log_subj "  if [%a] ~ [%a]" pp t pp u in
      List.iter fn to_solve
    end;
  (* Solving the constraints. *)
  match Unif.(solve builtins false {no_problems with to_solve}) with
  | Some(cs) ->
      let is_constr c =
        let eq_comm (t1,u1) (t2,u2) =
          (Eval.eq_modulo t1 t2 && Eval.eq_modulo u1 u2) ||
          (Eval.eq_modulo t1 u2 && Eval.eq_modulo t2 u1)
        in
        List.exists (eq_comm c) lhs_constrs
      in
      let cs = List.filter (fun c -> not (is_constr c)) cs in
      if cs <> [] then
        begin
          let fn (t,u) = fatal_msg "Cannot solve [%a] ~ [%a]\n" pp t pp u in
          List.iter fn cs;
          fatal r.pos  "Unable to prove SR for rule [%a]." pp_rule (s,h,r.elt)
        end
  | None     ->
      fatal r.pos "Rule [%a] does not preserve typing." pp_rule (s,h,r.elt)
