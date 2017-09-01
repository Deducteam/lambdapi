open Bindlib

(* AST *)
type term =
  | Vari of term var
  | Type
  | Kind
  | Prod of term * (term,term) binder
  | Abst of term * (term,term) binder
  | Appl of term * term

type tbox = term bindbox

type tvar = term var

(* Bindlib's "mkfree" *)
let mkfree : term var -> term =
  fun x -> Vari(x)

(* Smart constructors *)
let t_type : tbox = box Kind
let t_kind : tbox = box Kind

let t_prod : tbox -> string -> (tvar -> tbox) -> tbox =
  fun a x f -> box_apply2 (fun a b -> Prod(a,b)) a (vbind mkfree x f)

let t_abst : tbox -> string -> (tvar -> tbox) -> tbox =
  fun a x f -> box_apply2 (fun a b -> Abst(a,b)) a (vbind mkfree x f)

let t_appl : tbox -> tbox -> tbox =
  box_apply2 (fun t u -> Appl(t,u))

(* Context *)
type ctxt =
  | Empty
  | ConsT of ctxt * term var * term
  | ConsK of ctxt * term var * term

let rec find : term var -> ctxt -> term = fun x ctx ->
  match ctx with
  | Empty          -> raise Not_found
  | ConsT(ctx,y,b) -> if eq_vars x y then b else find x ctx
  | ConsK(ctx,y,b) -> if eq_vars x y then b else find x ctx

(* Evaluation *)
let rec whnf : term -> term = fun t ->
  match t with
  | Appl(t,u) ->
      begin
        match t with
        | Abst(_,f) -> whnf (subst f (whnf u))
        | t         -> Appl(t, whnf u)
      end
  | _         -> t

(* Equality *)
let rec eq : term -> term -> bool = fun a b ->
  let eq_binder f g =
    let x = free_of (new_var mkfree "dummy") in
    eq (subst f x) (subst g x)
  in
  let a = whnf a in
  let b = whnf b in
  match (a,b) with
  | (Vari(x)  , Vari(y)  ) -> eq_vars x y
  | (Type     , Type     ) -> true
  | (Kind     , Kind     ) -> true
  | (Prod(a,f), Prod(b,g)) -> eq a b && eq_binder f g
  | (Abst(a,f), Abst(b,g)) -> eq a b && eq_binder f g
  | (Appl(t,u), Appl(f,g)) -> eq t f && eq u g
  | (_        , _        ) -> false

(* Binding a subterm *)
let rec bind_term : term -> term -> (term, term) binder = fun t b ->
  let x = new_var mkfree "x" in
  let rec build : term -> tbox = fun b ->
    if eq b t then box_of_var x else
    match b with
    | Vari(x)   -> box_of_var x
    | Type      -> t_type
    | Kind      -> t_kind
    | Prod(a,b) -> t_prod (build a) (binder_name b)
                     (fun x -> build (subst b (free_of x)))
    | Abst(a,t) -> t_abst (build a) (binder_name t)
                     (fun x -> build (subst t (free_of x)))
    | Appl(t,u) -> t_appl (build t) (build u)
  in
  unbox (bind_var x (build b))

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

let bind_vari : term var -> term -> (term,term) binder = fun x t ->
  unbox (bind_var x (lift t))

(* Judgements *)
let rec well_formed : ctxt -> bool = fun ctx ->
  match ctx with
  | Empty          -> true
  | ConsT(ctx,x,a) -> well_formed ctx && has_type ctx a Type
  | ConsK(ctx,x,a) -> well_formed ctx && has_type ctx a Kind

and infer : ctxt -> term -> term = fun ctx t ->
  match t with
  | Vari(x)   -> find x ctx
  | Type      -> Kind
  | Kind      -> raise Not_found
  | Prod(a,b) -> let x = new_var mkfree (binder_name b) in
                 let b = subst b (free_of x) in
                 infer (ConsT(ctx,x,a)) b
  | Abst(a,t) -> let x = new_var mkfree (binder_name t) in
                 let t = subst t (free_of x) in
                 let b = infer (ConsT(ctx,x,a)) t in
                 Prod(a, bind_vari x b)
  | Appl(t,u) -> begin
                   match infer ctx t with
                   | Prod(a,b) -> subst b u
                   | _         -> raise Not_found
                 end

and has_type : ctxt -> term -> term -> bool = fun ctx t a ->
  let a = whnf a in
  match (t, a) with
  (* Sort *)
  | (Type     , Kind     ) -> well_formed ctx
  (* Variable *)
  | (Vari(x)  , a        ) -> well_formed ctx
                              && eq (find x ctx) a
  (* Product *)
  | (Prod(a,b), Type     ) -> let x = new_var mkfree (binder_name b) in
                              let b = subst b (free_of x) in
                              let new_ctx = ConsT(ctx,x,a) in
                              has_type ctx a Type
                              && has_type new_ctx b Type
  (* Product 2 *)
  | (Prod(a,b), Kind     ) -> let x = new_var mkfree (binder_name b) in
                              let b = subst b (free_of x) in
                              let new_ctx = ConsT(ctx,x,a) in
                              has_type ctx a Type
                              && has_type new_ctx b Kind
  (* Abstraction and Abstraction 2 *)
  | (Abst(a,t), Prod(c,b)) -> let x = new_var mkfree (binder_name b) in
                              let t = subst t (free_of x) in
                              let b = subst b (free_of x) in
                              let new_ctx = ConsT(ctx,x,a) in
                              eq a c
                              && has_type ctx a Type
                              && (has_type new_ctx b Type
                                  || has_type new_ctx b Kind)
                              && has_type new_ctx t b
  (* Application *)
  | (Appl(t,u), b        ) -> let a = infer ctx u in
                              let b = bind_term u b in
                              has_type ctx t (Prod(a,b))
                              && has_type ctx u a
  (* No rule apply. *)
  | (_        , _        ) -> false

(* Parser *)
type p_term =
  | P_Vari of string
  | P_Type
  | P_Kind
  | P_Prod of string * p_term * p_term
  | P_Abst of string * p_term * p_term
  | P_Appl of p_term * p_term

let parser ident = ''[a-zA-Z]+''
let parser expr (p : [`Func | `Appl | `Atom]) =
  (* Variable *)
  | x:ident
      when p = `Atom
      -> P_Vari(x)
  (* Type constant *)
  | "Type"
      when p = `Atom
      -> P_Type
  (* Kind constant *)
  | "Kind"
      when p = `Atom
      -> P_Kind
  (* Product *)
  | "Π" x:ident ":" a:(expr `Atom) "." b:(expr `Func)
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

let parse : string -> p_term =
  Earley.(handle_exception (parse_string (expr `Func) (blank_regexp "[ ]*")))

type context = (string * term var) list

let find_ident : string -> context -> term var = fun x vars ->
  try List.assoc x vars with Not_found ->
    Printf.eprintf "Unbound variable %S...\n%!" x; exit 1

let to_term : context -> p_term -> term = fun vars t ->
  let rec build : context -> p_term -> tbox = fun vars t ->
    match t with
    | P_Vari(x)     -> box_of_var (find_ident x vars)
    | P_Type        -> t_type
    | P_Kind        -> t_kind
    | P_Prod(x,a,b) -> t_prod (build vars a) x
                         (fun v -> build ((x,v)::vars) b)
    | P_Abst(x,a,t) -> t_abst (build vars a) x
                         (fun v -> build ((x,v)::vars) t)
    | P_Appl(t,u)   -> t_appl (build vars t) (build vars u)
  in
  unbox (build vars t)

let parse_term : context -> string -> term = fun vars str ->
  to_term vars (parse str)

(* Tests *)
let _ =
  let _X = new_var mkfree "X" in
  let ctx = ConsK(Empty, _X, Type) in
  let vars = [("X", _X)] in
  let id = parse_term vars "λx:X.x" in
  let ty = parse_term vars "Πx:X.X" in
  assert (has_type ctx id ty);
  assert (not (has_type ctx ty id));
  Printf.printf "OK!\n%!"
