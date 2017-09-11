open Bindlib

let debug = ref false

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
  | Prod of term * (term,term) binder
  | Abst of term * (term,term) binder
  | Appl of term * term
  | Unif of term option ref

type tbox = term bindbox

type tvar = term var

type rule =
  { definition  : (term, term * term) mbinder
  ; constructor : term var
  ; arity       : int }

(* Bindlib's "mkfree" *)
let mkfree : term var -> term =
  fun x -> Vari(x)

(* Smart constructors *)
let t_type : tbox = box Type
let t_kind : tbox = box Kind

let t_prod : tbox -> string -> (tvar -> tbox) -> tbox =
  fun a x f -> box_apply2 (fun a b -> Prod(a,b)) a (vbind mkfree x f)

let t_abst : tbox -> string -> (tvar -> tbox) -> tbox =
  fun a x f -> box_apply2 (fun a b -> Abst(a,b)) a (vbind mkfree x f)

let t_appl : tbox -> tbox -> tbox =
  box_apply2 (fun t u -> Appl(t,u))

(* Pattern data *)
let pattern_data : term -> (term var * int) option = fun t ->
  let rec get_args acc t =
    match t with
    | Vari(x)   -> Some(x, acc)
    | Appl(t,u) -> get_args (u::acc) t
    | _         -> None
  in
  match get_args [] t with
  | None        -> None
  | Some(x, ts) -> Some(x, List.length ts)

(* Context *)
type ctxt =
  { variables : (term var * term) list
  ; rules     : rule list }

let empty_ctxt =
  {variables = []; rules = []} 

let add_var : term var -> term -> ctxt -> ctxt = fun x a ctx ->
  {ctx with variables = (x,a)::ctx.variables}

let add_rule : rule -> ctxt -> ctxt = fun r ctx ->
  {ctx with rules = r::ctx.rules}

let find_rules : term var -> int -> ctxt -> (int * rule) list = fun x i ctx ->
  let rec suitable acc rs =
    match rs with
    | []    -> acc
    | r::rs -> if eq_vars x r.constructor && r.arity <= i then
                 suitable ((i - r.arity, r)::acc) rs
               else suitable acc rs
  in suitable [] ctx.rules

let find : term var -> ctxt -> term = fun x ctx ->
  snd (List.find (fun (y,_) -> eq_vars x y) ctx.variables)

let find_name : string -> ctxt -> term var = fun x ctx ->
  fst (List.find (fun (y,_) -> name_of y = x) ctx.variables)

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
let rec print_term : out_channel -> term -> unit = fun oc t ->
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
  match t with
  | Vari(x)   -> output_string oc (name_of x)
  | Type      -> output_string oc "Type"
  | Kind      -> output_string oc "Kind"
  | Prod(a,b) ->
      let (x,b) = unbind mkfree b in
      let x = name_of x in
      let (l,r) = if is_abst a then ("(",")") else ("","") in
      if x = "_" then
        Printf.fprintf oc "%s%a%s ⇒ %a" l print_term a r print_term b
      else
        Printf.fprintf oc "%s%s:%a%s ⇒ %a" l x print_term a r print_term b
  | Abst(a,t) ->
      let (x,t) = unbind mkfree t in
      Printf.fprintf oc "λ%s:%a.%a" (name_of x) print_term a print_term t
  | Appl(t,u) ->
      let (l1,r1) = if is_abst t then ("(",")") else ("","") in
      let (l2,r2) = if is_appl u then ("(",")") else ("","") in
      Printf.fprintf oc "%s%a%s %s%a%s" l1 print_term t r1 l2 print_term u r2
  | Unif(r)   ->
      begin
        match !r with
        | None    -> output_string oc "?"
        | Some(t) -> print_term oc t
      end

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
  in print_vars oc ctx.variables

(* Evaluation *)
let rec rewrite : ctxt -> term -> term = fun ctx t ->
  match pattern_data t with
  | None      -> t
  | Some(x,i) ->
      let rs = find_rules x i ctx in
      let ts = List.rev_map (fun (i,r) -> match_term ctx i r t) rs in
      let ts = from_opt_rev ts in
      match ts with
      | []    -> t
      | [t]   -> t
      | t::ts ->
          let nb = List.length ts in
          Printf.eprintf "(WARN) %i other rules apply...\n%!" nb; t

and match_term : ctxt -> int -> rule -> term -> term option = fun ctx e r t ->
  let ar = mbinder_arity r.definition in
  let (l,r) = msubst r.definition (Array.init ar (fun _ -> Unif(ref None))) in
  let (t,args) = remove_args t e in
  if eq ~no_whnf:true ctx t l then Some(add_args r args) else None

and eval : ctxt -> term -> term = fun ctx t ->
  let t = rewrite ctx t in
  match t with
  | Appl(t,u) ->
      begin
        match t with
        | Abst(_,f) -> eval ctx (subst f (eval ctx u))
        | t         -> Appl(t, eval ctx u)
      end
  | _         -> t

(* Equality *)
and eq : ?no_whnf:bool -> ctxt -> term -> term -> bool =
  fun ?(no_whnf=false) ctx a b ->
  let eq_binder f g =
    let x = free_of (new_var mkfree "_eq_binder_") in
    eq ctx (subst f x) (subst g x)
  in
  let a = if no_whnf then a else eval ctx a in
  let b = if no_whnf then b else eval ctx b in
  match (a,b) with
  | (Vari(x)  , Vari(y)  ) -> eq_vars x y
  | (Type     , Type     ) -> true
  | (Kind     , Kind     ) -> true
  | (Prod(a,f), Prod(b,g)) -> eq ctx a b && eq_binder f g
  | (Abst(a,f), Abst(b,g)) -> eq ctx a b && eq_binder f g
  | (Appl(t,u), Appl(f,g)) -> eq ctx t f && eq ctx u g
  | (Unif(r)  , _        ) ->
      begin
        match !r with
        | None   -> r := Some(b); true
        | Some a -> eq ctx a b
      end
  | (_        , Unif(r)  ) ->
      begin
        match !r with
        | None   -> r := Some(a); true
        | Some b -> eq ctx a b
      end
  | (_        , _        ) -> false

let rec lift : term -> tbox = fun t ->
  match t with
  | Vari(x)   -> box_of_var x
  | Type      -> t_type
  | Kind      -> t_kind
  | Prod(a,b) -> t_prod (lift a) (binder_name b)
                   (fun x -> lift (subst b (free_of x)))
  | Abst(a,t) -> t_abst (lift a) (binder_name t)
                   (fun x -> lift (subst t (free_of x)))
  | Appl(t,u) -> t_appl (lift t) (lift u)
  | Unif(r)   -> (match !r with Some t -> lift t | None -> box t)

let bind_vari : term var -> term -> (term,term) binder = fun x t ->
  unbox (bind_var x (lift t))

(* Judgements *)
let rec infer : ctxt -> term -> term = fun ctx t ->
  match t with
  | Vari(x)   -> find x ctx
  | Type      -> Kind
  | Kind      -> raise Not_found
  | Prod(a,b) -> let x = new_var mkfree (binder_name b) in
                 let b = subst b (free_of x) in
                 infer (add_var x a ctx) b
  | Abst(a,t) -> let x = new_var mkfree (binder_name t) in
                 let t = subst t (free_of x) in
                 let b = infer (add_var x a ctx) t in
                 Prod(a, bind_vari x b)
  | Appl(t,u) -> begin
                   match infer ctx t with
                   | Prod(a,b) ->
                       let c = infer ctx u in
                       if eq ctx c a then subst b u
                       else raise Not_found
                   | _         ->
                       raise Not_found
                 end
  | Unif(r)   -> begin
                   match !r with
                   | None   -> raise Not_found
                   | Some t -> infer ctx t
                 end

and has_type : ctxt -> term -> term -> bool = fun ctx t a ->
  if !debug then
    begin
      Printf.printf "%a ⊢ %a : %a\n%!"
        print_ctxt ctx print_term t print_term a
    end;
  let a = eval ctx a in
  match (t, a) with
  (* Sort *)
  | (Type     , Kind     ) -> true
  (* Variable *)
  | (Vari(x)  , a        ) -> eq ctx (find x ctx) a
  (* Product *)
  | (Prod(a,b), Type     ) -> let x = new_var mkfree (binder_name b) in
                              let b = subst b (free_of x) in
                              has_type ctx a Type
                              && has_type (add_var x a ctx) b Type
  (* Product 2 *)
  | (Prod(a,b), Kind     ) -> let x = new_var mkfree (binder_name b) in
                              let b = subst b (free_of x) in
                              has_type ctx a Type
                              && has_type (add_var x a ctx) b Kind
  (* Abstraction and Abstraction 2 *)
  | (Abst(a,t), Prod(c,b)) -> let x = new_var mkfree (binder_name b) in
                              let t = subst t (free_of x) in
                              let b = subst b (free_of x) in
                              let ctx_x = add_var x a ctx in
                              eq ctx a c
                              && has_type ctx a Type
                              && (has_type ctx_x b Type
                                  || has_type ctx_x b Kind)
                              && has_type ctx_x t b
  (* Application *)
  | (Appl(t,u), b        ) ->
      begin
        match infer ctx t with
        | Prod(a,ba) as tt -> eq ctx (subst ba u) b
                              && has_type ctx t tt
                              && has_type ctx u a
        | _          -> false
      end
  (* No rule apply. *)
  | (_        , _        ) -> false

(* Parser *)
type p_term =
  | P_Vari of string
  | P_Type
  | P_Prod of string * p_term * p_term
  | P_Abst of string * p_term * p_term
  | P_Appl of p_term * p_term

let check_not_reserved id =
  if List.mem id ["Type"] then Earley.give_up ()

let parser ident = id:''[a-zA-Z]+'' -> check_not_reserved id; id
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
  (* Abstraction *)
  | "λ" x:ident ":" a:(expr `Atom) "." t:(expr `Func)
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
  | NewVar of string * p_term
  | Rule   of string list * p_term * p_term
  | Check  of p_term * p_term
  | Infer  of p_term
  | Eval   of p_term

let parser toplevel =
  | x:ident ":" a:expr                  -> NewVar(x,a)
  | "[" xs:ident* "]" t:expr "→" u:expr -> Rule(xs,t,u)
  | "#CHECK" t:expr "," a:expr          -> Check(t,a)
  | "#INFER" t:expr                     -> Infer(t)
  | "#EVAL" t:expr                      -> Eval(t)

let parser full = {l:toplevel "."}*

(** Blank function for basic blank characters (' ', '\t', '\r' and '\n')
    and line comments starting with "//". *)
let blank buf pos =
  let rec fn state prev ((buf0, pos0) as curr) =
    let (c, buf1, pos1) = Input.read buf0 pos0 in
    let next = (buf1, pos1) in
    match (state, c) with
    (* Basic blancs. *)
    | (`Ini, ' ' )
    | (`Ini, '\t')
    | (`Ini, '\r')
    | (`Ini, '\n') -> fn `Ini curr next
    (* Comment. *)
    | (`Ini, '/' ) -> fn `Opn curr next
    | (`Opn, '/' ) -> let p = (buf1, Input.line_length buf1) in fn `Ini p p
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

let to_tbox : ctxt -> p_term -> tbox = fun ctx t ->
  let rec build vars t =
    match t with
    | P_Vari(x)     -> let x =
                         try List.assoc x vars with Not_found ->
                         try find_name x ctx with Not_found ->
                         Printf.eprintf "Unbound variable %S...\n%!" x;
                         exit 1
                       in box_of_var x
    | P_Type        -> t_type
    | P_Prod(x,a,b) -> let f v =
                         build (if x = "_" then vars else (x,v)::vars) b
                       in
                       t_prod (build vars a) x f
    | P_Abst(x,a,t) -> let f v = build ((x,v)::vars) t in
                       t_abst (build vars a) x f
    | P_Appl(t,u)   -> t_appl (build vars t) (build vars u)
  in
  build [] t

let to_term : ctxt -> p_term -> term = fun ctx t ->
  unbox (to_tbox ctx t)

(* Interpret the term given as a string *)
let parse_term : ctxt -> string -> term = fun ctx str ->
  to_term ctx (parse str)

(* Interpret a whole file *)
let handle_file : ctxt -> string -> ctxt = fun ctx fname ->
  let handle_item : ctxt -> p_item -> ctxt = fun ctx it ->
    match it with
    | NewVar(x,a)  ->
        let a = to_term ctx a in
        let xx = new_var mkfree x in
        if has_type ctx a Type then
          begin
            Printf.printf "(type) %s\t= %a\n%!" x print_term a;
            add_var xx a ctx
          end
        else if has_type ctx a Kind then
          begin
            Printf.printf "(kind) %s\t= %a\n%!" x print_term a;
            add_var xx a ctx
          end
        else
          begin
            Printf.eprintf "Type error on %s...\n%!" x;
            exit 1
          end
    | Rule(xs,t,u) ->
        let xs = new_mvar mkfree (Array.of_list xs) in
        let add x ctx = add_var x (Unif(ref None)) ctx in
        let ctx_aux = Array.fold_right add xs ctx in
        let t = to_tbox ctx_aux t in
        let u = to_tbox ctx_aux u in
        let definition = unbox (bind_mvar xs (box_pair t u)) in
        let t = unbox t in
        let u = unbox u in
        begin
          match pattern_data t with
          | None      ->
              Printf.eprintf "Not a valid pattern...\n%!";
              exit 1
          | Some(x,i) ->
              let rule = {definition; constructor = x; arity = i} in
              try
                let tt = infer ctx_aux t in
                let tu = infer ctx_aux u in
                if not (eq ctx tt tu) then raise Not_found;
                Printf.printf "(rule) %a → %a\n%!" print_term t print_term u;
                add_rule rule ctx
              with Not_found ->
                Printf.eprintf "Ill-typed rule...\n%!";
                exit 1
        end
    | Check(t,a)   ->
        let t = to_term ctx t in
        let a = to_term ctx a in
        if has_type ctx t a then
          begin
            Printf.printf "(chck) %a : %a\n%!" print_term t print_term a;
            ctx
          end
        else
          begin
            Printf.eprintf "(chck) Type error...\n%!";
            exit 1
          end
    | Infer(t)     ->
        let t = to_term ctx t in
        begin
          try
            let a = infer ctx t in
            Printf.eprintf "(infr) %a : %a\n%!" print_term t print_term a
          with Not_found ->
            Printf.eprintf "(infr) %a : UNABLE TO INFER\n%!"
              print_term t
        end;
        ctx
    | Eval(t)      ->
        let t = to_term ctx t in
        let v = eval ctx t in
        Printf.eprintf "(eval) %a\n%!" print_term v;
        ctx
  in
  List.fold_left handle_item ctx (parse_file fname)

(* Run files *)
let _ =
  let ctx = ref empty_ctxt in
  for i = 1 to Array.length Sys.argv - 1 do
    ctx := handle_file !ctx Sys.argv.(i)
  done
