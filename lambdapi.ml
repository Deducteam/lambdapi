open Bindlib

let quiet       = ref false
let debug       = ref false
let debug_eval  = ref false
let debug_infer = ref false
let debug_patt  = ref false

let in_debug_mode : unit -> bool = fun () ->
  !debug || !debug_eval || !debug_infer || !debug_patt

let set_debug str =
  if String.contains str 's' then Earley.debug_lvl := 1;
  if String.contains str 'a' then debug := true;
  if String.contains str 'e' then debug_eval  := true;
  if String.contains str 'i' then debug_infer := true;
  if String.contains str 'p' then debug_patt  := true

let red fmt = "\027[31m" ^^ fmt ^^ "\027[0m%!"
let gre fmt = "\027[32m" ^^ fmt ^^ "\027[0m%!"
let yel fmt = "\027[33m" ^^ fmt ^^ "\027[0m%!"
let blu fmt = "\027[34m" ^^ fmt ^^ "\027[0m%!"
let mag fmt = "\027[35m" ^^ fmt ^^ "\027[0m%!"
let cya fmt = "\027[36m" ^^ fmt ^^ "\027[0m%!"

let log name fmt = Printf.eprintf ((cya "[%s] ") ^^ fmt ^^ "\n%!") name

let out fmt =
  let fmt = if in_debug_mode () then mag fmt else fmt in
  let fmt = fmt ^^ "%!" in
  if !quiet then Printf.ifprintf stdout fmt
  else Printf.printf fmt

let err fmt = Printf.eprintf (red fmt)
let wrn fmt = Printf.eprintf (yel fmt)

let from_opt_rev : 'a option list -> 'a list = fun l ->
  let fn acc e =
    match e with
    | None   -> acc
    | Some e -> e::acc
  in
  List.fold_left fn [] l

(* AST *)
type term =
  | Vari of term var
  | Type
  | Kind
  | Symb of symbol
  | Prod of term * ttbinder
  | Abst of term * ttbinder
  | Appl of term * term
  | Unif of term option ref

and  ttbinder = (term, term) binder

and  sym =
  { sym_name  : string
  ; sym_type  : term }

and  def =
  { def_name  : string
  ; def_type  : term
  ; def_rules : rule list ref }

and  symbol =
  | Sym of sym
  | Def of def

and  rule =
  { defin : (term, term * term) mbinder
  ; arity : int }

let symbol_name : symbol -> string = fun s ->
  match s with
  | Sym(sym) -> sym.sym_name
  | Def(def) -> def.def_name

let symbol_type : symbol -> term = fun s ->
  match s with
  | Sym(sym) -> sym.sym_type
  | Def(def) -> def.def_type

(* Signature *)
module Sign =
  struct
    type t =
      { syms  : (string, sym) Hashtbl.t
      ; defs  : (string, def) Hashtbl.t }
 
    let create : unit -> t = fun () ->
      let syms  = Hashtbl.create 37 in
      let defs  = Hashtbl.create 37 in
      { syms ; defs }

    let name_exists : string -> t -> bool = fun n sign ->
      Hashtbl.mem sign.syms n || Hashtbl.mem sign.defs n

    let new_sym : t -> string -> term -> unit = fun sign name ty ->
      if name_exists name sign then wrn "Redefinition of %s.\n" name;
      let sym = { sym_name = name ; sym_type = ty } in
      Hashtbl.add sign.syms name sym
 
    let new_def : t -> string -> term -> unit = fun sign name ty ->
      if name_exists name sign then wrn "Redefinition of %s.\n" name;
      let def = { def_name = name ; def_type = ty ; def_rules = ref [] } in
      Hashtbl.add sign.defs name def
 
    let find_symbol : t -> string -> symbol = fun sign name ->
      try Sym (Hashtbl.find sign.syms name)
      with Not_found -> Def (Hashtbl.find sign.defs name)
  end

(* Bindlib related things and smart constructors. *)
type tbox = term bindbox
type tvar = term var

let mkfree : term var -> term =
  fun x -> Vari(x)

let t_type : tbox = box Type

let t_kind : tbox = box Kind

let t_symb : Sign.t -> string -> tbox =
  fun sign n -> box (Symb (Sign.find_symbol sign n))

let t_prod : tbox -> string -> (tvar -> tbox) -> tbox =
  fun a x f -> box_apply2 (fun a b -> Prod(a,b)) a (vbind mkfree x f)

let t_abst : tbox -> string -> (tvar -> tbox) -> tbox =
  fun a x f -> box_apply2 (fun a b -> Abst(a,b)) a (vbind mkfree x f)

let t_appl : tbox -> tbox -> tbox =
  box_apply2 (fun t u -> Appl(t,u))

(* Lifting function *)
let rec lift : term -> tbox = fun t ->
  match t with
  | Vari(x)   -> box_of_var x
  | Type      -> t_type
  | Kind      -> t_kind
  | Symb(s)   -> box (Symb(s))
  | Prod(a,b) -> t_prod (lift a) (binder_name b)
                   (fun x -> lift (subst b (mkfree x)))
  | Abst(a,t) -> t_abst (lift a) (binder_name t)
                   (fun x -> lift (subst t (mkfree x)))
  | Appl(t,u) -> t_appl (lift t) (lift u)
  | Unif(r)   -> (match !r with Some t -> lift t | None -> box t)

let update_names : term -> term = fun t -> unbox (lift t)

(* Equality of binders. *)
let eq_binder : (term -> term -> bool) -> ttbinder -> ttbinder -> bool =
  fun eq f g -> f == g ||
    let x = mkfree (new_var mkfree "_eq_binder_") in
    eq (subst f x) (subst g x)

(* Unfolding of unification variables. *)
let rec unfold : term -> term = fun t ->
  match t with
  | Unif(r) -> (match !r with Some(t) -> unfold t | None -> t) 
  | _       -> t

(* Occurence check. *)
let rec occurs : term option ref -> term -> bool = fun r t ->
  match unfold t with
  | Prod(a,b) -> occurs r a || occurs r (subst b Kind)
  | Abst(a,t) -> occurs r a || occurs r (subst t Kind)
  | Appl(t,u) -> occurs r t || occurs r u
  | Unif(u)   -> u == r
  | Type      -> false
  | Kind      -> false
  | Vari(_)   -> false
  | Symb(_)   -> false

(* Context *)
type ctxt = (term var * term) list

let empty_ctxt = []

let add_var : term var -> term -> ctxt -> ctxt =
  fun x a ctx -> (x,a)::ctx

let find : term var -> ctxt -> term = fun x ctx ->
  snd (List.find (fun (y,_) -> eq_vars x y) ctx)

let remove_args : term -> int -> term * term list = fun t n ->
  let rec rem acc n t =
    assert (n >= 0);
    match (t, n) with
    | (_        , 0) -> (t, acc)
    | (Appl(t,u), n) -> rem (u::acc) (n-1) t
    | (_        , _) -> assert false
  in
  rem [] n t

let add_args : term -> term list -> term =
  List.fold_left (fun t u -> Appl(t,u))

(* Printing *)
let print_term : out_channel -> term -> unit = fun oc t ->
  let rec is_abst t =
    match t with
    | Abst(_,_) -> true
    | Prod(_,_) -> true
    | Unif(r)   -> (match !r with None -> false | Some t -> is_abst t)
    | _         -> false
  in
  let rec is_appl t =
    match t with
    | Appl(_,_) -> true
    | Abst(_,_) -> true
    | Unif(r)   -> (match !r with None -> false | Some t -> is_appl t)
    | _         -> false
  in
  let rec print oc t =
    match t with
    | Vari(x)   -> output_string oc (name_of x)
    | Type      -> output_string oc "Type"
    | Kind      -> output_string oc "Kind"
    | Symb(s)   -> output_string oc (symbol_name s)
    | Prod(a,b) ->
        let (x,b) = unbind mkfree b in
        let x = name_of x in
        let (l,r) = if is_abst a then ("(",")") else ("","") in
        if x = "_" then Printf.fprintf oc "%s%a%s ⇒ %a" l print a r print b
        else Printf.fprintf oc "%s%s:%a%s ⇒ %a" l x print a r print b
    | Abst(a,t) ->
        let (x,t) = unbind mkfree t in
        Printf.fprintf oc "λ%s:%a.%a" (name_of x) print a print t
    | Appl(t,u) ->
        let (l1,r1) = if is_abst t then ("(",")") else ("","") in
        let (l2,r2) = if is_appl u then ("(",")") else ("","") in
        Printf.fprintf oc "%s%a%s %s%a%s" l1 print t r1 l2 print u r2
    | Unif(r)   ->
        begin
          match !r with
          | None    -> output_string oc "?"
          | Some(t) -> print oc t
        end
  in
  print oc (update_names t)

let print_ctxt : out_channel -> ctxt -> unit = fun oc ctx ->
  let rec print_vars oc ls =
    match ls with
    | []          ->
        output_string oc "∅"
    | [(x,a)]     ->
        let x = name_of x in
        if x = "_" then output_string oc "∅"
        else Printf.fprintf oc "%s : %a" x print_term a
    | (x,a)::ctx  ->
        let x = name_of x in
        if x = "_" then print_vars oc ctx
        else Printf.fprintf oc "%a, %s : %a" print_vars ctx x print_term a
  in print_vars oc ctx

(* Strict equality (no conversion). *)
let unify : term option ref -> term -> bool =
  fun r a -> not (occurs r a) && (r := Some(a); true)

let eq : term -> term -> bool = fun a b ->
  if !debug then log "equa" "%a =!= %a" print_term a print_term b;
  let rec eq a b = a == b ||
    match (unfold a, unfold b) with
    | (Vari(x)      , Vari(y)      ) -> eq_vars x y
    | (Type         , Type         ) -> true
    | (Kind         , Kind         ) -> true
    | (Symb(Sym(sa)), Symb(Sym(sb))) -> sa == sb
    | (Symb(Def(sa)), Symb(Def(sb))) -> sa == sb
    | (Prod(a,f)    , Prod(b,g)    ) -> eq a b && eq_binder eq f g
    | (Abst(a,f)    , Abst(b,g)    ) -> eq a b && eq_binder eq f g
    | (Appl(t,u)    , Appl(f,g)    ) -> eq t f && eq u g
    | (Unif(r1)     , Unif(r2)     ) when r1 == r2 -> true
    | (Unif(r)      , b            ) -> unify r b
    | (a            , Unif(r)      ) -> unify r a
    | (_            , _            ) -> false
  in
  let res = eq a b in
  if !debug then
    begin
      let c = if res then gre else red in
      log "equa" (c "%a =!= %a") print_term a print_term b;
    end;
  res

(* Evaluation *)
let rec eval : Sign.t -> term -> term = fun sign t ->
  if !debug_eval then log "eval" "evaluating %a" print_term t;
  let rec eval_aux sign t stk =
    let t = unfold t in
    match (t, stk) with
    (* Push. *)
    | (Appl(t,u)   , stk    ) -> eval_aux sign t (eval_aux sign u [] :: stk)
    (* Beta. *)
    | (Abst(_,f)   , v::stk ) -> eval_aux sign (subst f v) stk
    (* Try to rewrite. *)
    | (Symb(Def(s)), stk    ) ->
        begin
          let nb_args = List.length stk in
          let rs = List.filter (fun r -> r.arity <= nb_args) !(s.def_rules) in
          let match_term rule t stk =
            let ar = mbinder_arity rule.defin in
            let uvars = Array.init ar (fun _ -> Unif(ref None)) in
            let (l,r) = msubst rule.defin uvars in
            if !debug_eval then
              log "eval" "RULE %a → %a" print_term l print_term r;
            let rec add_n_args n t stk =
              match (n, stk) with
              | (0, stk   ) -> (t, stk)
              | (i, v::stk) -> add_n_args (i-1) (Appl(t,v)) stk
              | (_, _     ) -> assert false
            in
            let (t, stk) = add_n_args rule.arity t stk in
            if eq t l then Some(add_args r stk) else None
          in
          let ts = List.rev_map (fun r -> match_term r t stk) rs in
          let ts = from_opt_rev ts in
          let nb = List.length ts in
          if !debug_eval && nb > 1 then wrn "%i rules apply...\n%!" nb;
          match ts with
          | []   -> add_args t stk
          | t::_ -> eval_aux sign t []
        end
    (* In head normal form. *)
    | (t           , stk    ) -> add_args t stk
  in
  let u = eval_aux sign t [] in
  if !debug_eval then log "eval" "produced %a" print_term u; u

(* Equality *)
let eq_modulo : Sign.t -> term -> term -> bool = fun sign a b ->
  if !debug then log "equa" "%a == %a" print_term a print_term b;
  let rec get_head acc t =
    match unfold t with
    | Appl(t,u) -> get_head (u::acc) t
    | t         -> (t, acc)
  in
  let rec eq_mod a b = eq a b ||
    let a = eval sign a in
    let b = eval sign b in
    eq a b ||
    let (ha, argsa) = get_head [] a in
    let (hb, argsb) = get_head [] b in
    let rigid = ref true in
    begin
      match (ha, hb) with
      | (Vari(x)      , Vari(y)      ) -> eq_vars x y
      | (Type         , Type         ) -> true
      | (Kind         , Kind         ) -> true
      | (Symb(Sym(sa)), Symb(Sym(sb))) -> rigid := false; sa == sb
      | (Symb(Def(sa)), Symb(Def(sb))) -> sa == sb
      | (Prod(a,f)    , Prod(b,g)    ) -> eq_mod a b && eq_binder eq_mod f g
      | (Abst(a,f)    , Abst(b,g)    ) -> eq_mod a b && eq_binder eq_mod f g
      | (Appl(_,_)    , _            ) -> assert false
      | (_            , Appl(_,_)    ) -> assert false
      | (Unif(r1)     , Unif(r2)     ) when r1 == r2 -> true
      | (Unif(r)      , b            ) -> unify r b
      | (a            , Unif(r)      ) -> unify r a
      | (_            , _            ) -> false
    end &&
    try List.for_all2 (if !rigid then eq else eq_mod) argsa argsb
    with Invalid_argument(_) -> false
  in
  let res = eq_mod a b in
  if !debug then
    begin
      let c = if res then gre else red in
      log "equa" (c "%a == %a") print_term a print_term b;
    end;
  res

let bind_vari : term var -> term -> (term,term) binder = fun x t ->
  unbox (bind_var x (lift t))

(* Judgements *)
let rec infer : Sign.t -> ctxt -> term -> term = fun sign ctx t ->
  let rec infer ctx t =
    if !debug_infer then
      log "INFR" "%a ⊢ %a : ?" print_ctxt ctx print_term t;
    let a =
      match unfold t with
      | Vari(x)   -> find x ctx
      | Type      -> Kind
      | Kind      -> err "Kind has not type...\n";
                     raise Not_found
      | Symb(s)   -> symbol_type s
      | Prod(a,b) -> let x = new_var mkfree (binder_name b) in
                     let b = subst b (mkfree x) in
                     begin
                       match infer (add_var x a ctx) b with
                       | Kind -> Kind
                       | Type -> Type 
                       | _    ->
                           err "Expected Type / Kind for [%a]...\n"
                             print_term b;
                           raise Not_found
                     end
      | Abst(a,t) -> let x = new_var mkfree (binder_name t) in
                     let t = subst t (mkfree x) in
                     let b = infer (add_var x a ctx) t in
                     Prod(a, bind_vari x b)
      | Appl(t,u) -> begin
                       match unfold (infer ctx t) with
                       | Prod(a,b) ->
                           if has_type sign ctx u a then subst b u
                           else
                             begin
                               err "Cannot show [%a : %a]...\n"
                                 print_term u print_term a;
                               raise Not_found
                             end
                       | a         ->
                           err "Product expected for [%a], found [%a]...\n"
                             print_term t print_term a;
                           raise Not_found
                     end
      | Unif(_)   -> assert false
    in
    if !debug_infer then
      log "INFR" "%a ⊢ %a : %a" print_ctxt ctx print_term t print_term a;
    eval sign a
  in
  if !debug then
    log "infr" "%a ⊢ %a : ?" print_ctxt ctx print_term t;
  let a = infer ctx t in
  if !debug then
    log "infr" "%a ⊢ %a : %a" print_ctxt ctx print_term t print_term a;
  (* assert (has_type sign ctx t a); *) a

and has_type : Sign.t -> ctxt -> term -> term -> bool = fun sign ctx t a ->
  let rec has_type ctx t a =
    match (unfold t, eval sign a) with
    (* Sort *)
    | (Type     , Kind     ) -> true
    (* Variable *)
    | (Vari(x)  , a        ) -> eq_modulo sign (find x ctx) a
    (* Symbol *)
    | (Symb(s)  , a        ) -> eq_modulo sign (symbol_type s) a
    (* Product *)
    | (Prod(a,b), Type     ) -> let x = new_var mkfree (binder_name b) in
                                let b = subst b (mkfree x) in
                                has_type ctx a Type
                                && has_type (add_var x a ctx) b Type
    (* Product 2 *)
    | (Prod(a,b), Kind     ) -> let x = new_var mkfree (binder_name b) in
                                let b = subst b (mkfree x) in
                                has_type ctx a Type
                                && has_type (add_var x a ctx) b Kind
    (* Abstraction and Abstraction 2 *)
    | (Abst(a,t), Prod(c,b)) -> let x = new_var mkfree (binder_name b) in
                                let t = subst t (mkfree x) in
                                let b = subst b (mkfree x) in
                                let ctx_x = add_var x a ctx in
                                eq_modulo sign a c
                                && has_type ctx a Type
                                && (has_type ctx_x b Type
                                    || has_type ctx_x b Kind)
                                && has_type ctx_x t b
    (* Application *)
    | (Appl(t,u), b        ) ->
        begin
          match infer sign ctx t with
          | Prod(a,ba) as tt -> eq_modulo sign (subst ba u) b
                                && has_type ctx t tt
                                && has_type ctx u a
          | _          -> false
        end
    (* Unification variable. *)
    | (Unif(_)  , _        ) ->
        true (* Only for patterns. FIXME FIXME FIXME ??!! *)
    (* No rule apply. *)
    | (_        , _        ) -> false
  in
  if !debug then
    log "type" "%a ⊢ %a : %a" print_ctxt ctx print_term t print_term a;
  let res = has_type ctx t a in
  if !debug then
    log "type" ((if res then gre else red) "%a ⊢ %a : %a")
      print_ctxt ctx print_term t print_term a;
  res


(* Parser *)
type p_term =
  | P_Vari of string
  | P_Type
  | P_Prod of string * p_term * p_term
  | P_Abst of string * p_term * p_term
  | P_Appl of p_term * p_term
  | P_Wild

let check_not_reserved id =
  if List.mem id ["Type"] then Earley.give_up ()

let parser ident = id:''[a-zA-Z0-9][_a-zA-Z0-9]*'' ->
  check_not_reserved id; id

let parser expr (p : [`Func | `Appl | `Atom]) =
  (* Variable *)
  | x:ident
      when p = `Atom
      -> P_Vari(x)
  (* Type constant *)
  | "Type"
      when p = `Atom
      -> P_Type
  (* Product *)
  | x:{ident ":"}?["_"] a:(expr `Appl) "⇒" b:(expr `Func)
      when p = `Func
      -> P_Prod(x,a,b)
  (* Wildcard *)
  | "_"
      when p = `Atom
      -> P_Wild
  (* Abstraction *)
  | "λ" x:ident ":" a:(expr `Func) "." t:(expr `Func)
      when p = `Func
      -> P_Abst(x,a,t)
  (* Application *)
  | t:(expr `Appl) u:(expr `Atom)
      when p = `Appl
      -> P_Appl(t,u)
  (* Parentheses *)
  | "(" t:(expr `Func) ")"
      when p = `Atom
  (* Coercions *)
  | t:(expr `Appl)
      when p = `Func
  | t:(expr `Atom)
      when p = `Appl

let expr = expr `Func

type p_item =
  | NewSym of bool * string * p_term
  | Rule   of string list * p_term * p_term
  | Check  of p_term * p_term
  | Infer  of p_term
  | Eval   of p_term
  | Conv   of p_term * p_term

let parser def =
  | "def" -> true
  | EMPTY -> false

let parser toplevel =
  | d:def x:ident ":" a:expr            -> NewSym(d,x,a)
  | "[" xs:ident* "]" t:expr "→" u:expr -> Rule(xs,t,u)
  | "#CHECK" t:expr "," a:expr          -> Check(t,a)
  | "#INFER" t:expr                     -> Infer(t)
  | "#EVAL" t:expr                      -> Eval(t)
  | "#CONV" t:expr "," u:expr           -> Conv(t,u)

let parser full = {l:toplevel "."}*

(** Blank function for basic blank characters (' ', '\t', '\r' and '\n')
    and line comments starting with "//". *)
let blank buf pos =
  let rec fn state prev ((buf0, pos0) as curr) =
    let open Input in
    let (c, buf1, pos1) = read buf0 pos0 in
    let next = (buf1, pos1) in
    match (state, c) with
    (* Basic blancs. *)
    | (`Ini, ' ' )
    | (`Ini, '\t')
    | (`Ini, '\r')
    | (`Ini, '\n') -> fn `Ini curr next
    (* Comment. *)
    | (`Ini, '/' ) -> fn `Opn curr next
    | (`Opn, '/' ) -> let p = normalize buf1 (line_length buf1) in fn `Ini p p
    (* Other. *)
    | (`Opn, _   ) -> prev
    | (`Ini, _   ) -> curr
  in
  fn `Ini (buf, pos) (buf, pos)

let parse_file : string -> p_item list =
  Earley.(handle_exception (parse_file full blank))

let parse : string -> p_term =
  Earley.(handle_exception (parse_string expr blank))

type context = (string * term var) list

let wildcards : term var list ref = ref []
let wildcard_counter = ref (-1)
let new_wildcard : unit -> tbox = fun () ->
  incr wildcard_counter;
  let x = new_var mkfree (Printf.sprintf "#%i#" !wildcard_counter) in
  wildcards := x :: !wildcards; box_of_var x

type env = (string * tvar) list

let to_tbox : bool -> env -> Sign.t -> p_term -> tbox =
  fun allow_wild vars sign t ->
    let rec build vars t =
      match t with
      | P_Vari(x)     ->
          begin
            try box_of_var (List.assoc x vars) with Not_found ->
            try t_symb sign x with Not_found ->
            err "Unbound variable %S...\n%!" x;
            exit 1
          end
      | P_Type        ->
          t_type
      | P_Prod(x,a,b) ->
          let f v = build (if x = "_" then vars else (x,v)::vars) b in
          t_prod (build vars a) x f
      | P_Abst(x,a,t) ->
          let f v = build ((x,v)::vars) t in
          t_abst (build vars a) x f
      | P_Appl(t,u)   ->
          t_appl (build vars t) (build vars u)
      | P_Wild        ->
          if not allow_wild then
            begin
              err "Wildcards \"_\" are only allowed in patterns...\n";
              exit 1
            end;
          new_wildcard ()
    in
    build vars t

let to_term : ?vars:env -> Sign.t -> p_term -> term =
  fun ?(vars=[]) sign t -> unbox (to_tbox false vars sign t)

let to_tbox_wc : ?vars:env -> Sign.t -> p_term -> tbox * term var array =
  fun ?(vars=[]) sign t ->
    wildcards := []; wildcard_counter := -1;
    let t = to_tbox true vars sign t in
    (t, Array.of_list !wildcards)

(* Interpret a whole file *)
let handle_file : Sign.t -> string -> unit = fun sign fname ->
  let handle_item : p_item -> unit = fun it ->
    match it with
    | NewSym(d,x,a) ->
        let a = to_term sign a in
        let sort =
          if has_type sign empty_ctxt a Type then "Type" else
          if has_type sign empty_ctxt a Kind then "Kind" else
          begin
            err "%s is neither of type Type nor Kind.\n" x;
            exit 1
          end
        in
        let kind = if d then "defi" else "symb" in
        out "(%s) %s : %a (of sort %s)\n" kind x print_term a sort;
        if d then Sign.new_def sign x a else Sign.new_sym sign x a
    | Rule(xs,t,u) ->
        let vars = List.map (fun x -> (x, new_var mkfree x)) xs in
        let ctx = List.map (fun (_,x) -> (x, Unif(ref None))) vars in
        let (t, wcs) = to_tbox_wc ~vars sign t in
        let u = to_tbox false vars sign u in
        let xs = Array.append (Array.of_list (List.map snd vars)) wcs in
        let defin = unbox (bind_mvar xs (box_pair t u)) in
        let t = unbox (bind_mvar wcs t) in
        let new_unif _ = Unif(ref None) in
        let wcs_args = Array.init (Array.length wcs) new_unif in
        let t = msubst t wcs_args in
        let u = unbox u in
        let pattern_data : term -> (def * int) option = fun t ->
          let rec get_args acc t =
            match unfold t with
            | Symb(Def(s)) -> Some(s, acc)
            | Appl(t,u)    -> get_args (u::acc) t
            | _            -> None
          in
          match get_args [] t with
          | None        -> None
          | Some(x, ts) -> Some(x, List.length ts)
        in
        begin
          match pattern_data t with
          | None      ->
              err "%a is not a valid pattern...\n" print_term t;
              exit 1
          | Some(s,i) ->
              let rule = { defin ; arity = i } in
              let infer t =
                try infer sign ctx t with Not_found ->
                  err "Unable to infer the type of [%a]\n" print_term t;
                  exit 1
              in
              let tt = infer t in
              if !debug_patt then
                begin
                  log "left" "Context for %a:" print_term t;
                  let fn (x,a) =
                    log "left" "  %s : %a" (name_of x) print_term a
                  in
                  List.iter fn ctx;
                  let fn i a =
                    log "left" "  #%i# = %a" i print_term a
                  in
                  Array.iteri fn wcs_args
                end;
              let tu = infer u in
              if !debug_patt then
                begin
                  log "left" "LHS: %a" print_term tt;
                  log "left" "RHS: %a" print_term tu
                end;
              if eq_modulo sign tt tu then
                begin
                  out "(rule) %a → %a\n" print_term t print_term u;
                  s.def_rules := !(s.def_rules) @ [rule]
                end
              else
                begin
                  err "[%a → %a] is ill-typed\n" print_term t print_term u;
                  err "Left : %a\n" print_term tt;
                  err "Right: %a\n" print_term tu;
                  exit 1
                end
        end
    | Check(t,a)   ->
        let t = to_term sign t in
        let a = to_term sign a in
        if has_type sign empty_ctxt t a then
          out "(chck) %a : %a\n" print_term t print_term a
        else
          begin
            err "%a does not have type %a...\n" print_term t print_term a;
            exit 1
          end
    | Infer(t)     ->
        let t = to_term sign t in
        begin
          try
            let a = infer sign empty_ctxt t in
            out "(infr) %a : %a\n" print_term t print_term a
          with Not_found ->
            err "%a : unable to infer\n%!" print_term t;
        end
    | Eval(t)      ->
        let t = to_term sign t in
        out "(eval) %a\n" print_term (eval sign t)
    | Conv(t,u)    ->
        let t = to_term sign t in
        let u = to_term sign u in
        if not (eq_modulo sign t u) then
          err "unable to convert %a and %a...\n" print_term t print_term u
        else
          out "(conv) OK\n"
  in
  List.iter handle_item (parse_file fname)

(* Run files *)
let _ =
  let usage = Sys.argv.(0) ^ " [--debug str] [--quiet] [FILE] ..." in
  let spec =
    [ ("--debug", Arg.String set_debug, "Set debugging mode.")
    ; ("--quiet", Arg.Set quiet       , "No output."         ) ]
  in
  let files = ref [] in
  let anon fn = files := fn :: !files in
  Arg.parse spec anon usage;
  let files = List.rev !files in
  let sign = Sign.create () in
  List.iter (handle_file sign) files
