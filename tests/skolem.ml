  open Common
  open Core open Term open Print
  open Parsing

  (** Builtin configuration for propositional logic. *)
  type config =
    { symb_ex  : sym (** Exists(∃) symbol. *)
    ; symb_all : sym (** Forall(∀) symbol. *) }

  (** [get_config ss pos] build the configuration using [ss]. *)
  let get_config : Sig_state.t -> Pos.popt -> config = fun ss pos ->
    let builtin = Builtin.get ss pos in
    { symb_ex  = builtin "ex"
    ; symb_all = builtin "all" }

  (**Pour dev uniquement : Permet de parser des termes en passant par une
  commande lambdapi. A remplacer par une extension du parser pour pouvoir
  tester sur des fichiers .lp*)
  let parse_term s =
    (* A hack to parse a term: wrap term [s] into [compute s;]. *)
    let c = "compute " ^ s ^ ";" in
    let command = (Stream.next (Parser.Lp.parse_string "term" c)) in
    match command.elt with
    | Syntax.P_query {elt=Syntax.P_query_normalize (t, _); _} -> t
    | _ -> assert false
  
  (*let parse_declaration s =
    let declaration = (Stream.next (Parser.Lp.parse_file s)) in
    match declaration.elt with
    | Syntax.P_command {elt=Syntax.P_symbol (s); _} -> s
    | _ -> assert false*)
  
  (**Pour dev uniquement : A partir des termes parsés (pterm), construit
  des Core.term *)
  let scope_term ss = Scope.scope_term true ss []

  (**Pour dev uniquement : Création d'une signature restreinte à laquelle
  on ajoutera quelques symboles pour tester le code. A remplacer par une fonction
  config*)
  let new_sig_state : Sig_state.t =
    let sign = Sig_state.create_sign (Sign.ghost_path "skl_test") in
    Sig_state.of_sign sign

  let add_sym ss id =
    Sig_state.add_symbol ss Public Defin Eager true (Pos.none id) Term.mk_Kind []
      None

  let sig_state = new_sig_state
  (**Création de la signature. *)

  (*let symb_Set = parse_term "constant symbol Set : TYPE;" |> scope_term sig_state 
  let symb_El  = parse_term "injective symbol El : Set → TYPE;" |> scope_term sig_state
  let symb_A  = parse_term "injective symbol A : Set;" |> scope_term sig_state
  let symb_B  = parse_term "injective symbol B : Set → Set;" |> scope_term sig_state*)

  let sig_state, symb_p = add_sym sig_state "P"
  let sig_state, symb_x = add_sym sig_state "*"
  let sig_state = Sig_state.add_notation sig_state symb_x (Sign.Prefix 1.)
  (*Déclaration du symbole existentiel + notation quantifier. *)
  (*quantifier Allows to write `f x, t instead of f (λ x, t): *)
  let sig_state, symb_ex = add_sym sig_state "∃"
  let sig_state = Sig_state.add_notation sig_state symb_ex Sign.Quant
  let sig_state, symb_all = add_sym sig_state "∀"
  let sig_state = Sig_state.add_notation sig_state symb_all Sign.Quant
  let sig_state, symb_not = add_sym sig_state "¬"

  let sig_state, symb_Set = Sig_state.add_symbol sig_state Public Const Eager true (Pos.none "Set") Term.mk_Type [] None
  (**Définition du type dépendant probablement pas correct *)
  let sig_state, symb_El = Sig_state.add_symbol sig_state Public Const Eager true (Pos.none "El") (Term.mk_Appl (Term.mk_Symb symb_Set, Term.mk_Type)) [] None
  let sig_state, symb_A = Sig_state.add_symbol sig_state Public Const Eager true (Pos.none "A") (Term.mk_Symb symb_Set) [] None
  let sig_state, symb_B = Sig_state.add_symbol sig_state Public Const Eager true (Pos.none "B") (Term.mk_Appl (Term.mk_Symb symb_Set, Term.mk_Symb symb_Set)) [] None

  (*Le contexte de la skolémisation permet de mémoriser les variables
  universelles. *)
  let empty_context = []

  let add_ctxt : ctxt->tvar->term->ctxt = 
    fun c var typ ->
      (var, typ, None):: c


  (*Debug : Pattern matching vérifie si [t_abs] est bien une
  abstraction, et affiche ses composantes. *)
  let decompose_abst t_abs = (*term list -> unit *)
    match t_abs with
    | [Abst(t, n)] -> (*(term, tbinder) *)
      let a, b = Bindlib.unbind n in 
      Format.printf "Type abstraction : %a @." term t ; (*: term *)
      Format.printf "Variable : %a @." term (mk_Vari a) ; (*: tvar*)
      Format.printf "Formule : %a @." term b (*: term*)
    | _ -> Format.printf "Erreur décomposition abst"

  (*Debug : Prend en argument un terme et vérifie si il est
  constitué d'un symbole existentiel suivit d'une abstraction.
  TODO : renvoyer l'adbstraction si c'est ok. Sinon erreur*)
  (*Pour l'instant, ça sera une fonction term -> bool *)
  let precond_simple t = 
    let u, ts = get_args t in
    decompose_abst ts;
    (is_symb symb_ex u) && are_quant_args (ts)
  
  let get_tbinder : term -> tbinder =
    fun t_ex ->
      let u, t_abs = get_args t_ex in
        match t_abs with
        | [Abst(a, n)] -> n (*(tbinder) *)
        | _ -> failwith "Unable to get_tbinder : term is not an abs"


  (**Skolémisation*)
  (**Pour skolémiser ∃x, P*)
  (** 1. Fonction new_skf génère un nouveau symbole de fonction, appelée
  fonction de skolem. Soit [y_1, ..., y_n] l'ens des variables libres qui apparaissent
  dans le terme P. La fonction de skolem estun symbole d'arité n.*)
  (** 2. Substition dans P de la variable x par un symbole de fonction *)

  let new_skolem : Sig_state.t -> ctxt -> int -> term -> Sig_state.t * sym * int =
    fun ss ctx cpt ex_typ ->
      let name = if cpt > 0 then ("f"^(string_of_int (cpt))) else "c" in
      let maj_sig, n_sym = Sig_state.add_symbol ss Public Const Eager true (Pos.none name) (fst (Ctxt.to_prod ctx ex_typ)) []
      None   
      in
      maj_sig, n_sym,(cpt + 1) 



  (**Applique à un symbole de fonction [skf] la liste d'argument constituée
  des variables quantifiées universelle mémorisés contexte [c].
  Substitution de la variable quantifiée existentielle par l'application
  ainsi crée.*)
  let subst_app : ctxt -> tbinder -> sym -> term =
    fun c formule skf ->
      let args_list = List.map (fun (v, _, _) -> mk_Vari v) c in
      let f_term = mk_Symb skf in
      let f_appl=  add_args f_term args_list in
    (*mk_Symb skf construit un terme à partir du symbole skf.*)
    Bindlib.subst formule f_appl 


  let skolemisation : Sig_state.t -> term -> term = fun ss t ->
    let rec skolemisation ss ctx cpt t =  
      Format.printf "@. Skolemisation du terme t : %a @." term t;
      match get_args t with
      | Symb(s), [a;Abst(x, tb)] when s == symb_ex -> (** \exists *)
        let maj_ss, nv_sym, maj_cpt = new_skolem ss ctx cpt x in 
        let maj_term = subst_app ctx tb nv_sym in
        Format.printf "@. Ex : substitution de %a par %a @." term t term maj_term;
        skolemisation maj_ss ctx maj_cpt maj_term
      | Symb(s), [a;Abst(b, tb)] when s == symb_all -> 
          let var, f = Bindlib.unbind tb in
          let maj_ctx = add_ctxt ctx var a in
          let maj_f = skolemisation ss maj_ctx cpt f in
          let maj_tb = bind var lift maj_f in
          add_args (mk_Symb s) [a ; mk_Abst (b, maj_tb)]
      | _  -> t 
    in
    skolemisation ss empty_context 0 t

  let rec nnf t = 
    match get_args t with
    | Symb(s), [a;Abst(x, tb)] when s == symb_ex ->
      let var, p = Bindlib.unbind tb in
      let not_tb = bind var lift (nnf p) in
      add_args (mk_Symb symb_all) [a; mk_Abst(x, not_tb)]
    | Symb(s), [a; Abst(x, tb)] when s == symb_all -> (**Code redondant, remplacer par un ifdans  le match case *)
      let var, p = Bindlib.unbind tb in
      let not_tb = bind var lift (nnf p) in
      add_args (mk_Symb symb_ex) [a; mk_Abst(x, not_tb)]
      (**PB de distrib du not *)
    | Symb(s), tl when s == symb_not -> mk_Appl(nnf hd, tl)
    | (hd, tl) -> (add_args (mk_Appl (symb_not, a) hd tl)
      

  let _ = 

    (*let t = parse_term "∀ P (λ x1 : P, (∃ P (λ y1 : P, ∀ P (λ x2 : P, (∃ P (λ y2 : P, x1 x2 y1 y2))))))" |> scope_term sig_state in
    let t2 = parse_term "(∃ P (λ y2 : P, y2))" |> scope_term sig_state in
    let t = parse_term "∃ A (λ x : A, (∀ (B x) (λ y : (B x), P x y)))" |> scope_term sig_state in*)
    Format.print_string "@. Ligne 1";
    let t = parse_term "¬(∀ P (λ x:P, ∃ P (λ y : P, ∀ P (λ z : P, x y z))))" |> scope_term sig_state in
    let nt = nnf t in
    Format.print_string "@. Ligne 2";
    Format.printf "@.Terme entrée : %a @." term t;
    Format.printf "@.Terme en nnf : %a @." term nt;
    let _, _, l = get_args_len t in 
    Format.print_string "Nombres d'arguments : ";
    Format.print_int l;
    Format.print_newline ();
    (*let skt = (skolemisation sig_state t) in
    Format.printf "@.Terme skolémisé : %a @." term skt;*)