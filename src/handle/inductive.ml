(** Generation of induction principles.

   We only consider first-order dependent types (no functional
   arguments). Polymorphic types can be encoded by using codes. In case of a
   mutually defined types, we generate an induction for each type. A single
   induction principle can be defined from those individual induction
   principles by using a conjunction operator.

   In the OCaml code, the prefix "ind" is used for inductive types. The prefix
   "rec" is used for recursors, aka induction principles. *)

open Lplib
open Timed
open Common open Pos open Error open Name
open Core open Term open Print
open Parsing open Syntax

(** Logging function for generating of inductive principle. *)
let log_ind = Logger.make 'g' "indu" "induction principles generation"
let log_ind = log_ind.pp

(** Type for inductive type definitions. *)
type inductive = (sym * sym list) list

(** Builtin configuration for induction. *)
type config =
  { symb_Prop : sym (** : TYPE. Type of propositions. *)
  ; symb_prf  : sym (** : Prop → TYPE.
                        Interpretation of propositions as types. *) }

(** [get_config ss pos] build the configuration using [ss]. *)
let get_config : Sig_state.t -> Pos.popt -> config = fun ss pos ->
  let builtin = Builtin.get ss pos in
  { symb_Prop = builtin "Prop"
  ; symb_prf  = builtin "P" }

(** [prf_of p c ts t] returns the term [c.symb_prf (p t1 ... tn t)] where ts =
   [ts1;...;tsn]. *)
let prf_of : config -> var -> term list -> term -> term = fun c p ts t ->
  mk_Appl (mk_Symb c.symb_prf, mk_Appl (add_args (mk_Vari p) ts, t))

(** compute safe prefixes for predicate and constructor argument variables. *)
let gen_safe_prefixes : inductive -> string * string * string =
  let is_apx c = match c with 'a' | 'p' | 'x' -> true | _ -> false in
  fun ind_list ->
  let open Extra in
  let clashing_names =
    let add_name_from_sym idmap sym =
      let s = sym.sym_name in
      if s <> "" && is_apx s.[0] then
        match root_and_index sym.sym_name with
        | ("a"|"p"|"x"), _ -> add_name s idmap
        | _ -> idmap
      else idmap
    in
    let add_names_from_ind idmap (ind_sym, cons_sym_list) =
      let idmap = add_name_from_sym idmap ind_sym in
      List.fold_left add_name_from_sym idmap cons_sym_list
    in
    List.fold_left add_names_from_ind StrMap.empty ind_list
  in
  fst (get_safe_prefix "a" clashing_names),
  fst (get_safe_prefix "p" clashing_names),
  fst (get_safe_prefix "x" clashing_names)

(** Type of maps associating to every inductive type some data useful for
   generating the induction principles. *)
type data = { ind_var : var (** predicate variable *)
            ; ind_type : term (** predicate variable type *)
            ; ind_conclu : term (** induction principle conclusion *) }
type ind_pred_map = (sym * data) list

(** [ind_typ_with_codom pos ind_sym env codom x_str a] assumes that [a] is of
   the form [Π(i1:a1),...,Π(in:an), TYPE]. It then generates a [tbox] similar
   to this type except that [TYPE] is replaced by [codom [i1;...;in]]. The
   string [x_str] is used as prefix for the variables [ik]. *)
let ind_typ_with_codom :
      popt -> sym -> Env.t -> (term list -> term) -> string -> term -> term =
  fun pos ind_sym env codom x_str a ->
  let rec aux : var list -> int -> term -> term = fun xs k a ->
    match get_args a with
    | (Type, _) -> codom (List.rev_map mk_Vari xs)
    | (Prod(a,b), _) ->
        let name = x_str ^ string_of_int k in
        let (x,b) = unbind ~name b in
        mk_Prod (a, bind_var x (aux (x::xs) (k+1) b))
    | _ -> fatal pos "The type of %a is not supported" sym ind_sym
  in
  aux (List.map (fun (_,(v,_,_)) -> v) env) 0 a

(** [create_ind_pred_map pos c arity ind_list a_str p_str x_str] builds an
   [ind_pred_map] from [ind_list]. The resulting list is in reverse order wrt
   [ind_list]. [a_str] is used as prefix for parameter names, [p_str] is used
   as prefix for predicate variable names, and [x_str] is used as prefix for
   the names of the variable arguments of predicate variables. *)
let create_ind_pred_map :
      popt -> config -> int -> inductive -> string -> string -> string
      -> var array * Env.t * ind_pred_map =
  fun pos c arity ind_list a_str p_str x_str ->
  (* create parameters *)
  let vs = Array.init arity (new_var_ind a_str) in
  let env =
    match ind_list with
    | [] -> assert false (* there must be at least one type definition *)
    | (ind_sym, _) :: _ -> fst (Env.of_prod_using [] vs !(ind_sym.sym_type))
  in
  (* create the ind_pred_map *)
  let create_sym_pred_data i (ind_sym,_) =
    (* predicate variable *)
    let ind_var = new_var_ind p_str i in
    (* predicate type *)
    let codom ts =
      mk_Arro (add_args (mk_Symb ind_sym) ts, mk_Symb c.symb_Prop) in
    let a = snd (Env.of_prod_using [] vs !(ind_sym.sym_type)) in
    let ind_type = ind_typ_with_codom pos ind_sym env codom x_str a in
    (* predicate conclusion *)
    let codom ts =
      let x = new_var x_str in
      let t = bind_var x
          (prf_of c ind_var (List.remove_heads arity ts) (mk_Vari x)) in
      mk_Prod (add_args (mk_Symb ind_sym) ts, t)
    in
    let ind_conclu = ind_typ_with_codom pos ind_sym env codom x_str a in
    (ind_sym, {ind_var; ind_type; ind_conclu})
  in
  vs, env, List.rev_mapi create_sym_pred_data ind_list

(** [fold_cons_type] generates some value of type ['c] by traversing the
   structure of [cons_sym.sym_type] and accumulating some data of type ['a].

   [pos] is the position of the inductive command.

   [ind_pred_map] is defined above.

   [x_str] is a string used as prefix for generating variable names when
   deconstructing a product with [LibTerm.unbind_name].

   [ind_sym] is an inductive type symbol of [ind_pred_map].

   [cons_sym] is a constructor symbol of [ind_sym].

   [inj_var] injects traversed bound variables into the type ['var].

   [init] is the initial value of type ['a].

   The traversal is made by the function [fold : (xs : 'var list) -> (acc :
   'a) -> term -> 'c] below. It keeps track of the variables [xs] we went
   through (the last variable comes first) and some accumulator [acc] set to
   [init] at the beginning.

   During the traversal, there are several possible cases:

   1) If the argument is a product of the form [Π x:t, u] with [t] of the form
   [Π y₁:a₁, …, Π yₙ:aₙ, s ts] and [s] mapped to [p] in [ind_pred_map], then
   the result is [rec_dom t x' v next] where [x' = inj_var (length xs) x], [v
   = aux env s p ts x'], [env = y₁:a₁; …; yₙ:aₙ] and [next = fold (x'::xs)
   acc' u] is the result of the traversal of [u] with the list of variables
   extended with [x] and the accumulator [acc' = acc_rec_dom acc x' v].

   2) If the type argument is a product [Πx:t, u] not of the previous form,
   then the result is [nonrec_dom t x' next] where [next = fold (x'::xs) acc'
   u] and [acc' = acc_nonrec_dom acc x'].

   3) If the type argument is of the form [ind_sym ts], then the result is
   [codom ts xs acc].

   4) Any other case is an error. *)
let fold_cons_type
      (pos : popt)
      (ind_pred_map : ind_pred_map)
      (x_str : string)
      (ind_sym : sym)
      (vs : var array)
      (cons_sym : sym)
      (inj_var : int -> var -> 'var)
      (init : 'a)

      (aux : Env.t -> sym -> var -> term list -> 'var -> 'aux)
      (acc_rec_dom : 'a -> 'var -> 'aux -> 'a)
      (rec_dom : term -> 'var -> 'aux -> 'c -> 'c)

      (acc_nonrec_dom : 'a -> 'var -> 'a)
      (nonrec_dom : term -> 'var -> 'c -> 'c)

      (codom : 'var list -> 'a -> var -> term list -> 'c)

    : 'c =
  let rec fold : 'var list -> int -> 'a -> term -> 'c = fun xs n acc t ->
    match get_args t with
    | (Symb(s), ts) ->
        if s == ind_sym then
          let d = List.assq ind_sym ind_pred_map in
          codom xs acc d.ind_var ts
        else fatal pos "%a is not a constructor of %a"
               sym cons_sym sym ind_sym
    | (Prod(t,u), _) ->
       let name = x_str ^ string_of_int n in
       let x, u = unbind ~name u in
       let x = inj_var (List.length xs + n) x in
       begin
         let env, b = Env.of_prod [] "y" t in
         match get_args b with
         | (Symb(s), ts) ->
             begin
               match List.assq_opt s ind_pred_map with
               | Some d ->
                   let v = aux env s d.ind_var ts x in
                   let next = fold (x::xs) (n+1) (acc_rec_dom acc x v) u in
                   rec_dom t x v next
               | None ->
                   let next = fold (x::xs) (n+1) (acc_nonrec_dom acc x) u in
                   nonrec_dom t x next
             end
         | _ -> fatal pos "The type of %a is not supported" sym cons_sym
       end
    | _ -> fatal pos "The type of %a is not supported" sym cons_sym
  in
  let _, t = Env.of_prod_using [] vs !(cons_sym.sym_type) in
  fold (List.rev_mapi inj_var (Array.to_list vs)) 0 init t

(** [gen_rec_type c pos ind_list vs env ind_pred_map x_str] generates the
   induction principles for each type in the inductive definition [ind_list]
   defined at the position [pos] whose parameters are [vs]. [x_str] is
   a string used for prefixing variable names that are generated. Remark: in
   the generated induction principles, each recursive argument is followed by
   its induction hypothesis. For instance, with [inductive T:TYPE := c:
   T->T->T], we get [ind_T: Π p:T -> Prop, (Π x₀:T, π(p x₀)-> Π x₁:T, π(p
   x₁)-> π(p (c x₀ x₁)) -> Π x:T, π(p x)]. *)
let gen_rec_types :
      config -> popt -> inductive
      -> var array -> Env.t -> ind_pred_map -> string -> term list =
  fun c pos ind_list vs env ind_pred_map x_str ->
  let n = Array.length vs in

  (* [case_of ind_sym cons_sym] creates the clause for the constructor
     [cons_sym] in the induction principle of [ind_sym]. *)
  let case_of : sym -> sym -> term = fun ind_sym cons_sym ->
    (* 'var = var, 'a = unit, 'aux = unit, 'c = term *)
    (* the accumulator is not used *)
    let inj_var _ x = x in
    let init = () in
    (* aux computes the induction hypothesis *)
    let aux env _ p ts x =
      let v = Env.appl (mk_Vari x) env in
      let v = prf_of c p (List.remove_heads n ts) v in
      Env.to_prod env v
    in
    let acc_rec_dom _ _ _ = () in
    let rec_dom t x v next =
      mk_Prod (t, bind_var x (mk_Arro (v, next)))
    in
    let acc_nonrec_dom _ _ = () in
    let nonrec_dom t x next = mk_Prod (t, bind_var x next) in
    let codom xs _ p ts =
      prf_of c p (List.remove_heads n ts)
        (add_args (mk_Symb cons_sym) (List.rev_map mk_Vari xs))
    in
    fold_cons_type pos ind_pred_map x_str ind_sym vs cons_sym inj_var
      init aux acc_rec_dom rec_dom acc_nonrec_dom nonrec_dom codom
  in

  (* Generates an induction principle for each type. *)
  let gen_rec_type (_, d) =
    let add_clause_cons ind_sym cons_sym t =
      mk_Arro (case_of ind_sym cons_sym, t)
    in
    let add_clauses_ind (ind_sym, cons_sym_list) t =
      List.fold_right (add_clause_cons ind_sym) cons_sym_list t
    in
    let rec_typ = List.fold_right add_clauses_ind ind_list d.ind_conclu in
    let add_quantifier t (_,d) =
      mk_Prod (d.ind_type, bind_var d.ind_var t) in
    let rec_typ = List.fold_left add_quantifier rec_typ ind_pred_map in
    Env.to_prod env rec_typ
  in

  List.map gen_rec_type ind_pred_map

(** [rec_name ind_sym] returns the name of the induction principle associated
   to the inductive type symbol [ind_sym]. *)
let rec_name ind_sym = Escape.add_prefix "ind_" ind_sym.sym_name

(** [iter_rec_rules pos ind_list vs rec_sym_list ind_pred_map] generates the
   recursor rules for the inductive type definition [ind_list] as position
   [pos] with parameters [vs], recursors are [rec_sym_list] and
   [ind_pred_map].

   For instance, [inductive T : Π(i1:A1),..,Π(im:Am), TYPE := c1:T1 | .. |
   cn:Tn] generates a rule for each constructor. If [Ti = Π x1:B1,..,Π
   xk:Bk,T] then the rule for ci is [ind_T p pc1 .. pcn _ .. _ (ci x1 .. xk)
   --> pci x1 t1? ... xk tk?]  with m underscores, [tj? = ind_T p pc1 .. pcn _
   .. _ xj] if [Bj = T v1 ... vm], and nothing otherwise. *)
let iter_rec_rules :
      popt -> inductive -> var array -> ind_pred_map
      -> (p_rule -> unit) -> unit =
  fun pos ind_list vs ind_pred_map f ->
  (* Rules are declared after recursor declarations. *)
  let rules_pos = shift (List.length ind_list + 1) (pos_end pos) in
  let n = Array.length vs in

  (* variable name used for a recursor case argument *)
  let case_arg_name cons_sym = cons_sym.sym_name in

  (* [arec sym_ind ts t] generates the application of the recursor of
     [sym_ind] to the type parameters [ts] and the constructor argument
     [t]. *)
  let arec : sym -> term list -> p_term -> p_term = fun sym_ind ts t ->
    (* Note: there cannot be name clashes between pattern variable names and
       function symbol names since pattern variables are prefixed by $. *)
    let apatt t n = P.appl t (P.patt0 n) in
    let head = P.iden (rec_name sym_ind) in
    (* add a wildcard for each parameter *)
    let head = P.appl_wild head n in
    (* add a predicate variable for each inductive type *)
    let head =
      let apred (_,d) t = apatt t (base_name d.ind_var) in
      List.fold_right apred ind_pred_map head
    in
    (* add a case variable for each constructor *)
    let acase t cons_sym = apatt t (case_arg_name cons_sym) in
    let acases t (_, cons_sym_list) =
      List.fold_left acase t cons_sym_list
    in
    let head = List.fold_left acases head ind_list in
    P.appl (P.appl_wild head (List.length ts - n)) t
  in

  (* [gen_rule_cons ind_sym rec_sym cons_sym] generates the p_rule of the
     recursor [rec_sym] of the inductive type [ind_sym] for the constructor
     [cons_sym]. *)
  let gen_rule_cons : sym -> sym -> p_rule = fun ind_sym cons_sym ->
    (* 'var = p_term, 'aux = p_term, 'a = p_term, 'c = p_rule *)
    (* the accumulator is used to compute the RHS *)
    let inj_var n _ = P.patt0 ("x" ^ string_of_int n) in
    let init = P.patt0 (case_arg_name cons_sym) in
    (* aux computes the recursive call *)
    let aux env s _ ts x =
      let env_appl t env =
        List.fold_right (fun (_,(x,_,_)) t -> P.appl t (P.var x)) env t in
      let add_abst t (_,(x,_,_)) =
        P.abst (Some (Pos.none (base_name x))) t in
      List.fold_left add_abst (arec s ts (env_appl x env)) env
    in
    let acc_rec_dom acc x aux = P.appl (P.appl acc x) aux in
    let rec_dom _ _ _ next = next in
    let acc_nonrec_dom a x = P.appl a x in
    let nonrec_dom _ _ next = next in
    let codom xs rhs _ ts =
      let cons_arg = P.appl_list (P.iden cons_sym.sym_name) (List.rev xs) in
      Pos.make rules_pos (arec ind_sym ts cons_arg, rhs)
    in
    fold_cons_type pos ind_pred_map "" ind_sym vs cons_sym inj_var
      init aux acc_rec_dom rec_dom acc_nonrec_dom nonrec_dom codom
  in

  (* Iterate [f] over every rule. *)
  let g (ind_sym, cons_sym_list) =
    List.iter (fun cons_sym -> f (gen_rule_cons ind_sym cons_sym))
      cons_sym_list
  in
  List.iter g ind_list
