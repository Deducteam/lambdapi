(** Soundness of unification rules. *)
open Console
open Extra
open Pos
open Terms

type pre_unification_rule =
  { pre_ur_lhs: term list loc
  ; pre_ur_rhs:  (term_env, term) Bindlib.mbinder loc }

module List = struct
  include List

  (** [mem_eq eq x l] is [List.mem x l] with equality [eq]. *)
  let mem_eq : 'a eq -> 'a -> 'a list -> bool = fun eq needle hay ->
    try ignore (List.find (eq needle) hay); true with Not_found -> false

  (** [are_distinct ?eq l] returns [true] if all elements of [l] are
      pairwise distinct and false otherwise. *)
  let rec are_distinct : ?eq:('a eq) -> 'a list -> bool =
    fun ?(eq=Stdlib.(=)) l ->
    match l with
    | hd :: tl -> if mem_eq eq hd tl then false else are_distinct ~eq tl
    | []       -> true
end

(** [pp_tevar oc x] prints term with environment variable [x] to the channel
    [oc]. *)
let pp_tevar : tevar pp = fun oc x ->
  Format.pp_print_string oc (Bindlib.name_of x)

(** [to_sym t] returns [s] if [t] is of the form [Symb(s,_)] and fails
    otherwise. *)
let to_sym : term -> sym = fun t ->
  match t with Symb(s,_) -> s | _ -> assert false

let check : pre_unification_rule loc -> unit = fun p_pur ->
  let (p_lhs, p_rhs) = (p_pur.elt.pre_ur_lhs, p_pur.elt.pre_ur_rhs) in
  let _, rhst = Bindlib.unmbind p_rhs.elt in
  (* Retrieve the sub unification problems in the form (xi, Hi). *)
  let bindings : (tevar * term) list =
    let (h, args) = Basics.get_args rhst in
    assert (to_sym h == Unif.Hint.list);
    let f t = (* [f (xi ≡ Hi)] returns [(xi, Hi)] *)
      match Basics.get_args t with
      | (Symb(s, _), [TEnv(TE_Vari(x),_); u]) ->
          assert (s == Unif.Hint.atom);
          (x, u)
      | _                                     ->
          assert false (* Ill-formed hint. *)
    in
    List.map f args
  in
  (* Ensure that (xi)i are distinct pairwise. *)
  let eq_fst (x,_) (y,_) = Bindlib.eq_vars x y in
  if not (List.are_distinct ~eq:eq_fst bindings) then
    fatal p_rhs.pos "Only linear hint RHS allowed";
  (* [vars_closed (_,t)] raises an error if [t] depends on a variable in
     [bvars]. *)
  let bvars = List.map fst bindings in
  let vars_closed (_,t) =
    let tb = lift t in
    if List.exists (fun x -> Bindlib.occur x tb) bvars then
      fatal p_rhs.pos
        "RHS of sub-unification problems can't depend on hinted vars"
  in
  (* Ensure that ∀ (i, j), Hi does not depend on xj. *)
  List.iter vars_closed bindings;
  (* [subst_from_hints t] substitutes pattern variables in [t] by the values
     in [bindings]. *)
  (* FIXME: rather replace by meta variables and check type (as with SR). *)
  let subst_of_hints t =
    let rec subst t =
      match unfold t with
      | Appl(t,u)         -> Appl(subst t, subst u)
      | Patt(Some(_),s,_) -> (* Only variables used in rhs. *)
          let f (x,_) = String.equal s (Bindlib.name_of x) in
          snd (try List.find f bindings with Not_found -> assert false)
      | t           -> t
    in
    subst t
  in
  (* Ensure that hints are sound, that is, P[x1 ≔ H1, ..., xn ≔ Hn] is
     convertible with Q[x1 ≔ H1, ..., xn ≔ Hn]. *)
  begin match p_lhs.elt with
    | [t; u] ->
      let pp_binding oc (tev, t) =
        Format.fprintf oc "@[$%a ≔ %a@]" pp_tevar tev Print.pp t
      in
      if not (Eval.eq_modulo [] (subst_of_hints t) (subst_of_hints u)) then
        fatal p_pur.pos ("[%a]@ is@ not@ convertible@ with@ [%a]@ " ^^
                         "with@ substitution@ [%a]")
          Print.pp t Print.pp u (List.pp pp_binding ", ") bindings
    | _      -> assert false
  end;
