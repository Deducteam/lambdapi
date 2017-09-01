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
let t_type : tbox = box Type
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

let rec find_name : string -> ctxt -> term var = fun x ctx ->
  match ctx with
  | Empty          -> raise Not_found
  | ConsT(ctx,y,b) -> if name_of y = x then y else find_name x ctx
  | ConsK(ctx,y,b) -> if name_of y = x then y else find_name x ctx

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

(* Printing *)
let rec print_term : out_channel -> term -> unit = fun oc t ->
  match t with
  | Vari(x)   -> output_string oc (name_of x)
  | Type      -> output_string oc "Type"
  | Kind      -> output_string oc "Kind"
  | Prod(a,b) -> let (x,b) = unbind mkfree b in
                 Printf.fprintf oc "Π%s:%a.%a" (name_of x)
                   print_term a print_term b
  | Abst(a,t) -> let (x,t) = unbind mkfree t in
                 Printf.fprintf oc "λ%s:%a.%a" (name_of x)
                   print_term a print_term t
  | Appl(t,u) -> Printf.fprintf oc "(%a) (%a)" print_term t print_term u

let rec print_ctxt : out_channel -> ctxt -> unit = fun oc ctx ->
  match ctx with
  | Empty          -> output_string oc "∅"
  | ConsT(ctx,x,a) -> Printf.fprintf oc "%a, %s : %a : Type"
                        print_ctxt ctx (name_of x) print_term a
  | ConsK(ctx,x,a) -> Printf.fprintf oc "%a, %s : %a : Kind"
                        print_ctxt ctx (name_of x) print_term a

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
  Printf.printf "Proving: %a ⊢ %a : %a\n%!"
    print_ctxt ctx print_term t print_term a;
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
  | P_Arrw of p_term * p_term
  | P_Abst of string * p_term * p_term
  | P_Appl of p_term * p_term

let check_not_reserved id =
  if List.mem id ["Type"; "Kind"] then Earley.give_up ()

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
  (* Kind constant *)
  | "Kind"
      when p = `Atom
      -> P_Kind
  (* Product *)
  | "Π" x:ident ":" a:(expr `Atom) "." b:(expr `Func)
      when p = `Func
      -> P_Prod(x,a,b)
  (* Arrow *)
  | a:(expr `Atom) "⇒" b:(expr `Func)
      when p = `Func
      -> P_Arrw(a,b)
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
  | NewKVar of string * p_term
  | NewTVar of string * p_term
  | DoCheck of p_term * p_term

let parser toplevel =
  | "kind" "var" x:ident ":" a:expr -> NewKVar(x,a)
  | "type" "var" x:ident ":" a:expr -> NewTVar(x,a)
  | "check" t:expr ":" a:expr       -> DoCheck(t,a)

let parser full = {l:toplevel ";"}*

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

let to_term : ctxt -> p_term -> term = fun ctx t ->
  let rec build vars t =
    match t with
    | P_Vari(x)     -> let x =
                         try List.assoc x vars with Not_found ->
                         try find_name x ctx with Not_found ->
                         Printf.eprintf "Unbound variable %S...\n%!" x;
                         exit 1
                       in box_of_var x
    | P_Type        -> t_type
    | P_Kind        -> t_kind
    | P_Prod(x,a,b) -> t_prod (build vars a) x
                         (fun v -> build ((x,v)::vars) b)
    | P_Arrw(a,b)   -> t_prod (build vars a) "_" (fun _ -> build vars b)
    | P_Abst(x,a,t) -> t_abst (build vars a) x
                         (fun v -> build ((x,v)::vars) t)
    | P_Appl(t,u)   -> t_appl (build vars t) (build vars u)
  in
  unbox (build [] t)

(* Interpret the term given as a string *)
let parse_term : ctxt -> string -> term = fun ctx str ->
  to_term ctx (parse str)

(* Interpret a whole file *)
let handle_file : ctxt -> string -> ctxt = fun ctx fname ->
  let handle_item : ctxt -> p_item -> ctxt = fun ctx it ->
    match it with
    | NewKVar(x,a) -> let a = to_term ctx a in
                      let xx = new_var mkfree x in
                      if has_type ctx a Kind then ConsK(ctx,xx,a) else
                        begin
                          Printf.eprintf "(kind) Type error on %s...\n%!" x;
                          exit 1
                        end
    | NewTVar(x,a) -> let a = to_term ctx a in
                      let xx = new_var mkfree x in
                      if has_type ctx a Type then ConsT(ctx,xx,a) else
                        begin
                          Printf.eprintf "(type) Type error on %s...\n%!" x;
                          exit 1
                        end
    | DoCheck(t,a) -> let t = to_term ctx t in
                      let a = to_term ctx a in
                      if has_type ctx t a then ctx else
                        begin
                          Printf.eprintf "(check) Type error...\n%!";
                          exit 1
                        end
  in
  List.fold_left handle_item ctx (parse_file fname)

(* Run files *)
let _ =
  let ctx = ref Empty in
  for i = 1 to Array.length Sys.argv - 1 do
    ctx := handle_file !ctx Sys.argv.(i)
  done;
  Printf.printf "Done.\n%!"
