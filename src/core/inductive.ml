(** Generation of induction principles.

   We only consider first-order dependent types (no functional
   arguments). Polymorphic types can be encoded by using codes. In case of a
   mutually defined types, we generate an induction for each type. A single
   induction principle can be defined from those individual induction
   principles by using a conjunction operator.

   In the OCaml code, the prefix "ind" is used for inductive types. The prefix
   "rec" is used for recursors, aka induction principles. *)

open! Lplib
open Timed
open Pos
open Console
open Terms
open Print
open Syntax

(** Logging function for generating of inductive principle. *)
let log_ind = new_logger 'g' "indu" "generating induction principle"
let log_ind = log_ind.logger

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

(** [gen_ind_typ_codom pos ind_sym codom s] assumes that the type of [ind_sym]
   is of the form [Π(i1:a1),...,Π(in:an), TYPE]. It then generates a [tbox]
   similar to this type except that [TYPE] is replaced by [codom
   [i1;...;in]]. The string [s] is used as prefix for the variables [ik]. *)
let gen_ind_typ_codom : popt -> sym -> (tbox list -> tbox) -> string -> tbox =
  fun pos ind_sym codom s ->
  let rec aux : tvar list -> term -> tbox = fun xs a ->
    match Basics.get_args a with
    | (Type, _) -> codom (List.rev_map _Vari xs)
    | (Prod(a,b), _) ->
        let (x,b) = Basics.unbind_name b s in
        _Prod (lift a) (Bindlib.bind_var x (aux (x::xs) b))
    | _ -> fatal pos "The type of %a is not supported" pp_symbol ind_sym
  in aux [] !(ind_sym.sym_type)

(** [prf_of p c ts t] returns the term [c.symb_prf (p t1 ... tn t)] where ts =
   [ts1;...;tsn]. *)
let prf_of : config -> tvar -> tbox list -> tbox -> tbox = fun c p ts t ->
  _Appl_symb c.symb_prf [_Appl (_Appl_list (_Vari p) ts) t]

(** compute safe prefixes for predicate and constructor argument variables. *)
let gen_safe_prefixes : inductive -> string * string = fun ind_list ->
  let clashing_names =
    let add_name_from_sym set sym =
      let s = sym.sym_name in
      if s <> "" && (s.[0] = 'x' || s.[0] = 'p') then Extra.StrSet.add s set
      else set
    in
    let add_names_from_ind set (ind_sym, cons_sym_list) =
      let set = add_name_from_sym set ind_sym in
      List.fold_left add_name_from_sym set cons_sym_list
    in
    List.fold_left add_names_from_ind Extra.StrSet.empty ind_list
  in
  let p_str = Extra.get_safe_prefix "p" clashing_names in
  let x_str = Extra.get_safe_prefix "x" clashing_names in
  p_str, x_str

(** Type of association maps for associating some useful data for the
   generation of induction principles to each inductive type. *)
type ind_pred_map = (sym * (tvar * tbox * tbox)) list

(** [create_ind_pred_map pos c ind_list p_str x_str] builds an association
   list mapping each inductive type symbol of [ind_list] in reverse order to
   some data useful for generating the induction principles:

- a predicate variable (e.g. p)

- its type (e.g. Nat -> Prop)

- its conclusion (e.g. Πx, π (p x))

[p_str] is used as prefix for predicate variable names, and [x_str] as prefix
   for the names of the variable arguments of the predicate. *)
let create_ind_pred_map :
      popt -> config -> inductive -> string -> string -> ind_pred_map =
  fun pos c ind_list p_str x_str ->
  let prop = _Symb c.symb_Prop in
  let create_sym_pred_data i (ind_sym,_) =
    (* predicate variable *)
    let p_str = p_str ^ string_of_int i in
    let p = Bindlib.new_var mkfree p_str in
    (* predicate type *)
    let codom ts = _Impl (_Appl_symb ind_sym ts) prop in
    let p_type = gen_ind_typ_codom pos ind_sym codom p_str in
    (* predicate conclusion *)
    let codom ts =
      let x = Bindlib.new_var mkfree x_str in
      let t = Bindlib.bind_var x (prf_of c p ts (_Vari x)) in
      _Prod (_Appl_symb ind_sym ts) t
    in
    let conclusion = gen_ind_typ_codom pos ind_sym codom p_str in
    (ind_sym, (p, p_type, conclusion))
  in
  List.rev_mapi create_sym_pred_data ind_list

(** [fold_cons_type] generates some value of type ['c] by traversing the
   structure of [cons_sym.sym_type] and accumulating some data of type ['a].

   [pos] is the position of the inductive command.

   [ind_pred_map] is defined above.

   [var_prefix] is a string used as prefix for generating variable names when
   deconstructing a product with [Basics.unbind_name].

   [ind_sym] is an inductive type symbol of [ind_pred_map].

   [cons_sym] is a constructor symbol of [ind_sym].

   [init] is the initial value of type ['a].

   The traversal is made by the function [fold : (xs : 'var list) -> (acc :
   'a) -> term -> 'c] below. It keeps track of the variables [xs] we went
   through (the last variable comes first) and some accumulator [acc] set to
   [init] at the beginning.

   During the traversal, there are several possible cases:

   1) If the type argument is a product of the form [Πx:s ts, b], then the
   result is [rec_dom (s ts) x aux next] where [aux = aux_rec_dom s p ts x],
   [p] is the variable to which [s] is mapped in [ind_pred_map], and [next =
   fold (x::xs) acc' b] is the result of the traversal of [b] with the list of
   variables extended with [x] and the accumulator [acc' = acc_rec_dom acc x
   aux].

   2) If the type argument is a product [Πx:a, b] not of the previous form,
   then the result is [nonrec_dom a x next] where [next = fold (x::xs) acc' b]
   and [acc' = acc_nonrec_dom acc x].

   3) If the type argument is of the form [ind_sym ts], then the result is
   [codom ts xs acc].

   4) Any other case is an error. *)
let fold_cons_type
      (pos : popt)
      (ind_pred_map : ind_pred_map)
      (var_prefix : string)

      (ind_sym : sym)
      (cons_sym : sym)

      (inj_var : 'var list -> tvar -> 'var)

      (init : 'a)
      (aux_rec_dom : sym -> tvar -> term list -> 'var -> 'aux)
      (acc_rec_dom : 'a -> 'var -> 'aux -> 'a)
      (acc_nonrec_dom : 'a -> 'var -> 'a)

      (rec_dom : term -> 'var -> 'aux -> 'c -> 'c)
      (nonrec_dom : term -> 'var -> 'c -> 'c)
      (codom : 'var list -> 'a -> tvar -> term list -> 'c)

    : 'c =
  let rec fold : 'var list -> 'a -> term -> 'c = fun xs acc a ->
    match Basics.get_args a with
    | (Symb(s), ts) ->
        if s == ind_sym then
          let pred_var,_,_ = List.assq ind_sym ind_pred_map in
          codom xs acc pred_var ts
        else fatal pos "%a is not a constructor of %a"
               pp_symbol cons_sym pp_symbol ind_sym
    | (Prod(a,b), _) ->
       let (x,b) = Basics.unbind_name b var_prefix in
       let x = inj_var xs x in
       begin
         match Basics.get_args a with
         | (Symb(s), ts) ->
             begin
               match List.assq_opt s ind_pred_map with
               | Some (pred_var,_,_) ->
                   let aux = aux_rec_dom s pred_var ts x in
                   let next = fold (x::xs) (acc_rec_dom acc x aux) b in
                   rec_dom a x aux next
               | None ->
                   let next = fold (x::xs) (acc_nonrec_dom acc x) b in
                   nonrec_dom a x next
             end
         | _ -> fatal pos "The type of %a is not supported" pp_symbol cons_sym
       end
    | _ -> fatal pos "The type of %a is not supported" pp_symbol cons_sym
  in fold [] init !(cons_sym.sym_type)

(** [gen_rec_type ss pos ind_list] generates the induction principles for each
   type in the inductive definition [ind_list] defined at the position
   [pos]. Each recursive argument is followed by its induction hypothesis. For
   instance, with [inductive T:TYPE := c: T->T->T], we get [ind_T: Πp:T->Prop,
   (Πx0:T, π(p x0)-> Πx1:T, π(p x1)-> π(p (c x0 x1)) -> Πx:T, π(p x)]. *)
let gen_rec_types :
      config -> Sig_state.t -> popt -> inductive -> ind_pred_map -> string
      -> term list =
  fun c ss pos ind_list ind_pred_map var_prefix ->

  (* [case_of ind_sym cons_sym] creates the clause for the constructor
     [cons_sym] in the induction principle of [ind_sym]. *)
  let case_of : sym -> sym -> tbox = fun ind_sym cons_sym ->
    (* 'var = tvar, 'a = tbox, 'aux = tbox, 'c = tbox *)
    let inj_var _ x = x in
    let init = _Type in
    let aux_rec_dom _ p ts x = prf_of c p (List.map lift ts) (_Vari x) in
    let acc_rec_dom a _ _ = a in
    let acc_nonrec_dom a _ = a in
    let rec_dom a x aux next =
      _Prod (lift a) (Bindlib.bind_var x (_Impl aux next))
    in
    let nonrec_dom a x next = _Prod (lift a) (Bindlib.bind_var x next) in
    let codom xs _ p ts =
      prf_of c p (List.map lift ts)
        (_Appl_symb cons_sym (List.rev_map _Vari xs))
    in
    fold_cons_type pos ind_pred_map var_prefix ind_sym cons_sym inj_var
      init aux_rec_dom acc_rec_dom acc_nonrec_dom rec_dom nonrec_dom codom
  in

  (* Generates an induction principle for each type. *)
  let gen_rec_type (_, (_,_,conclusion)) =
    let add_clause_cons ind_sym cons_sym c =
      _Impl (case_of ind_sym cons_sym) c
    in
    let add_clauses_ind (ind_sym, cons_sym_list) c =
      List.fold_right (add_clause_cons ind_sym) cons_sym_list c
    in
    let rec_typ = List.fold_right add_clauses_ind ind_list conclusion in
    let add_quantifier c (_,(v,a,_)) = _Prod a (Bindlib.bind_var v c) in
    let rec_typ = List.fold_left add_quantifier rec_typ ind_pred_map in
    Bindlib.unbox rec_typ
    (* Check the type of rec_typ. *)
    (*match Typing.infer [] rec_typ with
    | Some t ->
        (match unfold t with
         | Type -> rec_typ
         | _ ->
             fatal pos "[%a] is of [%a] instead of TYPE.
                        Please, raise an issue."
               pp_term rec_typ pp_term t)
    | None   ->
        fatal pos "[%a] is not typable. Please, raise an issue."
          pp_term rec_typ*)
  in

  List.map gen_rec_type ind_pred_map

(** [iter_rec_rules pos ind_list rec_sym_list ind_pred_map] generates the
   recursor rules for the inductive type definition [ind_list] and associated
   recursors [rec_sym_list] and [ind_pred_map].

   For instance, [inductive T : Π(i1:A1),..,Π(im:Am), TYPE := c1:T1 | .. |
   cn:Tn] generates a rule for each constructor. If [Ti = Πx1:B1,..,Πxk:Bk,T]
   then the rule for ci is [ind_T p pc1 .. pcn _ .. _ (ci x1 .. xk) --> pci x1
   t1? ... xk tk? with m underscores, [tj? = ind_T p pc1 .. pcn _ .. _ xj] if
   [Bj = T v1 ... vm], and nothing otherwise. *)
let iter_rec_rules :
  popt -> inductive -> sym list -> ind_pred_map -> (p_rule -> unit) -> unit =
  fun pos ind_list rec_sym_list ind_pred_map f ->

  (* variable name used for a recursor case argument *)
  let rec_arg_name cons_sym = cons_sym.sym_name in

  (* [commond_head n] generates the common head of the rule LHS's of a
     recursor symbol of name [n]. *)
  let lhs_head : string -> p_term = fun sym_name ->
    let head = P.iden sym_name in
    (* Note: there cannot be name clashes between pattern variable names and
       function symbol names since pattern variables are prefixed by $. *)
    let add_patt t n = P.appl t (P.patt0 n) in
    (* add a predicate variable for each inductive type *)
    let head =
      let add_pred (_,(v,_,_)) head = add_patt head (Bindlib.name_of v) in
      List.fold_right add_pred ind_pred_map head
    in
    (* add a case variable for each constructor *)
    let add_case head cons_sym = add_patt head (rec_arg_name cons_sym) in
    let add_ind head (_, cons_sym_list) =
      List.fold_left add_case head cons_sym_list
    in
    List.fold_left add_ind head ind_list
  in

  (* [gen_rule_cons ind_sym rec_sym cons_sym] generates the p_rule of the
     recursor [rec_sym] of the inductive type [ind_sym] for the constructor
     [cons_sym]. *)
  let gen_rule_cons : sym -> sym -> sym -> p_rule =
    fun ind_sym rec_sym cons_sym ->
    (* 'var = p_term, 'a = p_term, 'c = p_rule *)
    let inj_var xs _ = P.patt0 ("x" ^ string_of_int (List.length xs)) in
    let init = P.patt0 (rec_arg_name cons_sym) in
    let aux_rec_dom s _ ts x =
      let lhs_head = lhs_head (Parser.add_prefix "ind_" s.sym_name) in
      let arg_type = P.appl_wild lhs_head (List.length ts) in
      P.appl arg_type x
    in
    let acc_rec_dom p x aux = P.appl (P.appl p x) aux in
    let acc_nonrec_dom p x = P.appl p x in
    let rec_dom _ _ _ next = next in
    let nonrec_dom _ _ next = next in
    let codom xs p _ ts =
      let rec_arg = P.fold_appl (P.iden cons_sym.sym_name) (List.rev xs) in
      let lhs_head = lhs_head rec_sym.sym_name in
      let lhs = P.appl (P.appl_wild lhs_head (List.length ts)) rec_arg in
      P.rule lhs p
    in
    fold_cons_type pos ind_pred_map "" ind_sym cons_sym inj_var
      init aux_rec_dom acc_rec_dom acc_nonrec_dom rec_dom nonrec_dom codom
  in

  (* Iterate [f] over every rule. *)
  let g (ind_sym, cons_sym_list) rec_sym =
    List.iter
      (fun cons_sym -> f (gen_rule_cons ind_sym rec_sym cons_sym))
      cons_sym_list
  in
  List.iter2 g ind_list rec_sym_list
