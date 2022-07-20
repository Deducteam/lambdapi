open Common
open Core
open Term
open Print
open Sig_state
open Pos
open Parsing

(*** Hack pour le debug ***)
let parse_term s =
  (* A hack to parse a term: wrap term [s] into [compute s;]. *)
  let c = "compute " ^ s ^ ";" in
  let command = Stream.next (Parser.Lp.parse_string "term" c) in
  match command.elt with
  | Syntax.P_query { elt = Syntax.P_query_normalize (t, _); _ } -> t
  | _ -> assert false

(*** Hack pour le debug ***)
let scope_term ?(ctx = []) ss = Scope.scope_term true ss ctx

(*** Hack pour le debug ***)
let add_sym (ss, slist) id =
  let ss, sym =
    Sig_state.add_symbol ss Public Defin Eager true (Pos.none id) Term.mk_Type
      [] None
  in
  (ss, sym :: slist)

(*** Hack pour le debug ***)
let sig_state : Sig_state.t =
  let sign = Sig_state.create_sign (Sign.ghost_path "") in
  Sig_state.of_sign sign

type config = {
  symb_P : sym;  (** Encoding of propositions. *)
  symb_T : sym;  (** Encoding of types. *)
  symb_or : sym;  (** Disjunction(∨) symbol. *)
  symb_and : sym;  (** Conjunction(∧) symbol. *)
  symb_imp : sym;  (** Implication(⇒) symbol. *)
  symb_bot : sym;  (** Bot(⊥) symbol. *)
  symb_top : sym;  (** Top(⊤) symbol. *)
  symb_not : sym;  (** Not(¬) symbol. *)
  symb_ex : sym;  (** Exists(∃) symbol. *)
  symb_all : sym;  (** Forall(∀) symbol. *)
}
(** Builtin configuration for propositional logic. *)

(** Hack debug -> a remplacer par la fonction get_config cf why3_tactic.ml**)
let fol_symb_str = [ "P"; "t"; "∨"; "∧"; "⇒"; "⊥"; "⊤"; "¬"; "∃"; "∀" ]

(** [get_config ss pos] build the configuration using [ss]. *)
let get_config slist =
  let get n = List.nth slist n in
  {
    symb_P = get 0;
    symb_T = get 1;
    symb_or = get 2;
    symb_and = get 3;
    symb_imp = get 4;
    symb_bot = get 5;
    symb_top = get 6;
    symb_not = get 7;
    symb_ex = get 8;
    symb_all = get 9;
  }

let mk_env symb_p =
  let tv = [ "A"; "B" ] in
  let rec aux e tlist =
    let tb_p = _Symb symb_p in
    match tlist with
    | hd :: tl -> aux (Env.add (new_tvar hd) tb_p None e) tl
    | [] -> e
  in
  aux Env.empty tv

type quant = { symb : sym; dom : term; var : tvar; typ : term }

let add_quant : quant list -> sym -> term -> tvar -> term -> quant list =
 fun qlist q d v t -> { symb = q; dom = d; var = v; typ = t } :: qlist

let mk_quant : term -> quant -> term =
 fun f q ->
  let tb = bind q.var lift f in
  add_args (mk_Symb q.symb) [ q.dom; mk_Abst (q.typ, tb) ]

let nnf_term : config -> term -> term =
 fun cfg t ->
  Printf.printf "------ Start nnf_term ------";
  let rec nnf_prop t =
    Format.printf "@.-___- Start nnf_prop -___- %a @." term t;
    match get_args t with
    | Symb s, [ t1; t2 ] when s == cfg.symb_and ->
        add_args (mk_Symb s) [ nnf_prop t1; nnf_prop t2 ]
    | Symb s, [ t1; t2 ] when s == cfg.symb_or ->
        add_args (mk_Symb s) [ nnf_prop t1; nnf_prop t2 ]
    | Symb s, [ t1; t2 ] when s == cfg.symb_imp ->
        add_args (mk_Symb cfg.symb_or) [ neg t1; nnf_prop t2 ]
    | Symb s, [ t ] when s == cfg.symb_not ->
        Format.printf "@.NNF Not t, with t = %a @." term t;
        neg t
    | Symb s, [ a; Abst (x, tb) ] when s == cfg.symb_all ->
        let var, p = Bindlib.unbind tb in
        let nnf_tb = bind var lift (nnf_prop p) in
        add_args (mk_Symb cfg.symb_all) [ a; mk_Abst (x, nnf_tb) ]
    | Symb s, [ a; Abst (x, tb) ] when s == cfg.symb_ex ->
        let var, p = Bindlib.unbind tb in
        let nnf_tb = bind var lift (nnf_prop p) in
        add_args (mk_Symb cfg.symb_ex) [ a; mk_Abst (x, nnf_tb) ]
    | Symb s, _ ->
        Format.printf "@.NNF Quel symbole ? : %a @." term (mk_Symb s);
        t
    | Abst (_, _), _ ->
        Format.printf "@.Etat ABS: %a @." term t;
        t
    | w, _ ->
        Format.printf "@.NNF puit: %a @." term w;
        t
  and neg t =
    Format.printf "@.**** Start Neg**** : %a @." term t;
    match get_args t with
    | Symb s, [] when s == cfg.symb_bot ->
        mk_Symb cfg.symb_top (*add_args (mk_Symb cfg.symb_bot) []*)
    | Symb s, [] when s == cfg.symb_top ->
        mk_Symb cfg.symb_bot (*add_args (mk_Symb cfg.symb_top) []*)
    | Symb s, [ t1; t2 ] when s == cfg.symb_and ->
        Format.printf "@.NEG : and -> %a @." term t;
        add_args (mk_Symb cfg.symb_or) [ neg t1; neg t2 ]
    | Symb s, [ t1; t2 ] when s == cfg.symb_or ->
        Format.printf "@.NEG : or -> %a @." term t;
        add_args (mk_Symb cfg.symb_and) [ neg t1; neg t2 ]
    | Symb s, [ t1; t2 ] when s == cfg.symb_imp ->
        Format.printf "@.NEG : imp -> %a @." term t;
        neg (nnf_prop t)
    | Symb s, [ nt ] when s == cfg.symb_not ->
        Format.printf "@.NEG : not -> %a @." term nt;
        nnf_prop nt
    | Symb s, [ a; Abst (x, tb) ] when s == cfg.symb_all ->
        let var, p = Bindlib.unbind tb in
        let neg_tb = bind var lift (neg p) in
        Format.printf "@.NEG : Forall -> %a @." term t;
        add_args (mk_Symb cfg.symb_ex) [ a; mk_Abst (x, neg_tb) ]
    | Symb s, [ a; Abst (x, tb) ] when s == cfg.symb_ex ->
        let var, p = Bindlib.unbind tb in
        let nnf_tb = bind var lift (neg p) in
        Format.printf "@.NEG : exists -> %a @." term t;
        add_args (mk_Symb cfg.symb_all) [ a; mk_Abst (x, nnf_tb) ]
    | w, _ ->
        Format.printf "@. NEG : terme atomique -> %a @." term w;
        add_args (mk_Symb cfg.symb_not) [ t ]
  in
  match get_args t with
  | Symb s, [ t ] when s == cfg.symb_P ->
      Format.printf "@.P of : %a @." term t;
      mk_Appl (mk_Symb cfg.symb_P, nnf_prop t)
  | _ -> failwith "Cant NNF a term that is not a Prop !"

let prenex_term cfg t =
  let rec prenex t =
    match get_args t with
    | Symb s, [ t1; t2 ] when s == cfg.symb_and ->
        let qlist1, sub1 = prenex t1 in
        let qlist2, sub2 = prenex t2 in
        let t = add_args (mk_Symb s) [ sub1; sub2 ] in
        let qlist = qlist1 @ qlist2 in
        (qlist, t)
    | Symb s, [ t1; t2 ] when s == cfg.symb_or ->
        let qlist1, sub1 = prenex t1 in
        let qlist2, sub2 = prenex t2 in
        let t = add_args (mk_Symb s) [ sub1; sub2 ] in
        let qlist = qlist1 @ qlist2 in
        (qlist, t)
    | Symb s, [ t1; t2 ] when s == cfg.symb_imp ->
        failwith "Prenex : symb_imp occurs but t must be NNF"
    | Symb s, [ nt ] when s == cfg.symb_not ->
        Format.printf "@.NEG : not -> %a @." term nt;
        let res =
          match nt with
          | Vari x -> ([], t)
          | Symb s -> ([], t)
          | _ -> failwith "Prenex : symb_not formula must be NNF"
        in
        res
    | Symb s, [ a; Abst (x, tb) ] when s == cfg.symb_all ->
        let var, f = Bindlib.unbind tb in
        let qlist, sf = prenex f in
        let qlist = add_quant qlist s a var x in
        (qlist, sf)
    | Symb s, [ a; Abst (x, tb) ] when s == cfg.symb_ex ->
        let var, f = Bindlib.unbind tb in
        let qlist, sf = prenex f in
        let qlist = add_quant qlist s a var x in
        (qlist, sf)
    | w, _ -> ([], t)
  in
  let qlist, f =
    match get_args t with
    | Symb s, [ t ] when s == cfg.symb_P ->
        Format.printf "@.P of : %a @." term t;
        prenex t
    | _ -> failwith "Cant PRENEX a term that is not a Prop !"
  in
  List.fold_left mk_quant f (List.rev qlist)

(*"P"; "t" ; "∨" ; "∧" ; "⇒" ; "⊥" ; "⊤" ; "¬" ; "∃"; "∀"*)

let _ =
  let sig_state, symlist =
    List.fold_left add_sym (sig_state, []) fol_symb_str
  in
  let symlist = List.rev symlist in
  let c = get_config symlist in
  let env = mk_env (List.nth symlist 0) in
  let t =
    parse_term "P (∀ P (λ x1 : A, ¬ (∃ B (λ y1, ∨ (∨ x1 y1) ⊥))))"
    |> scope_term ~ctx:env sig_state
  in
  Format.printf "@.Terme IN : %a @." term t;
  let nnt = nnf_term c t in
  Format.printf "@.Terme en NNF : %a @." term nnt;
  let f =
    parse_term "P (∨ (∀ P (λ x1, x1)) A)" |> scope_term ~ctx:env sig_state
  in
  let pf = prenex_term c t in
  Format.printf "@.Terme en PF : %a @." term pf

(*let add_type ss id = Sig_state.add_symbol ss Public Const Eager true (Pos.none
  id) mk_Type [] None

  let add_quant p id = let ss, ty = p in let quant_type = mk_Appl (mk_Appl
  (mk_Appl (ty, ty), ty), ty) in let ss, sym = Sig_state.add_symbol ss Public
  Const Eager true (Pos.none id) quant_type [] None in (add_notation ss sym
  Quant, sym)

  let add_binop p id = let ss, ty = p in let binop_type = mk_Appl (mk_Appl (ty,
  ty), ty) in let ss, sym = Sig_state.add_symbol ss Public Const Eager true
  (Pos.none id) binop_type [] None in (add_notation ss sym (Infix(Right, 5.)),
  sym)

  let add_const ss ty id ty = Sig_state.add_symbol ss Public Const Eager true
  (Pos.none id) ty [] None

  let add_unop ss ty id = let unop_type = mk_Appl (ty, ty) in let ss, sym =
  Sig_state.add_symbol ss Public Const Eager true (Pos.none id) unop_type []
  None in (add_notation ss sym (Prefix(3.)), sym)*)

(*let nnf_term : config -> term -> term = fun cfg t -> Printf.printf "------
  Start nnf_term ------" ; let symb_P = cfg.symb_P in let rec nnf_prop t =
  Format.printf "@.-___- Start nnf_prop -___- %a @." term t; match get_args t
  with | Symb(s), [t1; t2] when s == cfg.symb_and -> add_args (mk_Symb s)
  [nnf_prop t1; nnf_prop t2] | Symb(s), [t1; t2] when s == cfg.symb_or ->
  add_args (mk_Symb s) [nnf_prop t1; nnf_prop t2] | Symb(s), [t1; t2] when s ==
  cfg.symb_imp -> let subt1 = mk_Appl (mk_Symb symb_P, t1) in add_args (mk_Symb
  cfg.symb_or) [neg_term subt1; nnf_prop t2] | Symb(s), [t] when s ==
  cfg.symb_not -> Format.printf "@.NNF : Not : %a @." term t; let subt = mk_Appl
  (mk_Symb symb_P, t) in neg_term subt | Symb(s), [a;Abst(x,tb)] when s ==
  cfg.symb_all -> let var, p = Bindlib.unbind tb in let nnf_tb = bind var lift
  (nnf_prop p) in add_args (mk_Symb cfg.symb_all) [a; mk_Abst(x, nnf_tb)] |
  Symb(s), [a;Abst(x,tb)] when s == cfg.symb_ex -> let var, p = Bindlib.unbind
  tb in let nnf_tb = bind var lift (nnf_prop p) in add_args (mk_Symb
  cfg.symb_ex) [a; mk_Abst(x, nnf_tb)] | Symb(s), _ -> Format.printf "@.NNF Quel
  symbole ? : %a @." term (mk_Symb s); t | Abst(_, _), _ -> Format.printf "@.NNF
  Etat ABS: %a @." term t; t | w, _ -> Format.printf "@.NNF What: %a @." term w;
  t and neg_term t = let rec neg_prop t = Format.printf "@.**** Start
  Neg_prop**** : %a @." term t; match get_args t with | Symb(s), [] when s ==
  cfg.symb_bot -> add_args (mk_Symb cfg.symb_bot) [] | Symb(s), [] when s ==
  cfg.symb_top -> add_args (mk_Symb cfg.symb_top) [] | Symb(s), [t1; t2] when s
  == cfg.symb_and -> let subt1 = mk_Appl (mk_Symb symb_P, t1) in let subt2 =
  mk_Appl (mk_Symb symb_P, t2) in add_args (mk_Symb cfg.symb_or) [neg_term
  subt1; neg_term subt2] | Symb(s), [t1; t2] when s == cfg.symb_or ->
  Format.printf "@.neg : OR : %a @." term t; let subt1 = mk_Appl (mk_Symb
  symb_P, t1) in let subt2 = mk_Appl (mk_Symb symb_P, t2) in add_args (mk_Symb
  cfg.symb_and) [neg_term subt1; neg_term subt2] | Symb(s), [t1; t2] when s ==
  cfg.symb_imp -> neg_prop (nnf_prop t) | Symb(s), [nt] when s == cfg.symb_not
  -> Format.printf "@.neg : NOT : %a @." term nt; (match nt with | Symb(_) -> t
  | Vari (_) -> t | _ -> let subtnt = mk_Appl (mk_Symb symb_P, nt) in nnf_prop
  subtnt) | Symb(s), [a;Abst(x,tb)] when s == cfg.symb_all -> let var, p =
  Bindlib.unbind tb in let neg_tb = bind var lift (neg_prop p) in add_args
  (mk_Symb cfg.symb_ex) [a; mk_Abst(x, neg_tb)] | Symb(s), [a;Abst(x,tb)] when s
  == cfg.symb_ex ->

  let var, p = Bindlib.unbind tb in let nnf_tb = bind var lift (neg_prop p) in
  add_args (mk_Symb cfg.symb_all) [a; mk_Abst(x, nnf_tb)] | w, tl ->
  Format.printf "@.NEG What: %a @." term w; List.map (Format.printf "; %a ;"
  term) tl; t in match get_args t with | (Symb(s), [t]) when s == cfg.symb_P ->
  Format.printf "@.NEG get_args : %a @." term (mk_Symb s); neg_prop t | _ ->
  Format.printf "@.NEG fails : %a @." term t; failwith "Cant NEG a term that is
  not a Prop !" in match get_args t with | (Symb(s), [t]) when s == cfg.symb_P
  -> nnf_prop t | _ -> failwith "Cant NNF a term that is not a Prop !"

  let fol_symb_str = [ "P"; "t" ; "∨" ; "∧" ; "⇒" ; "⊥" ; "⊤" ; "¬" ; "∃"; "∀"
  ]*)
