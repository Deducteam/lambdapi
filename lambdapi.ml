open Bindlib

let debug       = ref false
let debug_eval  = ref false
let debug_infer = ref false

let set_debug str =
  if String.contains str 'p' then Earley.debug_lvl := 1;
  if String.contains str 'a' then debug := true;
  if String.contains str 'e' then debug_eval := true;
  if String.contains str 'i' then debug_infer := true

let red fmt = "\027[31m" ^^ fmt ^^ "\027[0m%!"
let yel fmt = "\027[33m" ^^ fmt ^^ "\027[0m%!"
let cya fmt = "\027[36m" ^^ fmt ^^ "\027[0m%!"

let log name fmt = Printf.eprintf ((cya "[%s] ") ^^ fmt ^^ "\n%!") name

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
  { defin : (term, term * term) mbinder
  ; const : term var
  ; arity : int }

(* Bindlib's "mkfree" *)
let mkfree : term var -> term =
  fun x -> Vari(x)

(* Unfolding of unification variables. *)
let rec unfold : term -> term = fun t ->
  match t with
  | Unif(r) -> (match !r with Some(t) -> unfold t | None -> t) 
  | _       -> t

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
let rec eval : ctxt -> term -> term = fun ctx t ->
  if !debug then log "eval" "evaluating %a" print_term t;
  let rec eval_aux ctx t stk =
    let t = unfold t in
    if !debug_eval then
      begin
        Printf.eprintf "EVAL_AUX (%a ∗" print_term t;
        List.iter (Printf.eprintf " [%a]" print_term) stk;
        Printf.eprintf "%s)\n%!" (if List.length stk = 0 then " ε" else "")
      end;
    match (t, stk) with
    (* Push. *)
    | (Appl(t,u), stk    ) -> eval_aux ctx t (eval_aux ctx u [] :: stk)
    (* Beta. *)
    | (Abst(_,f), v::stk ) -> eval_aux ctx (subst f v) stk
    (* Try to rewrite. *)
    | (Vari(x)  , stk    ) ->
        begin
          let nb_args = List.length stk in
          let suitable r = eq_vars x r.const && r.arity <= nb_args in
          let rs = List.filter suitable ctx.rules in
          let match_term rule t stk =
            let ar = mbinder_arity rule.defin in
            let uvars = Array.init ar (fun _ -> Unif(ref None)) in
            let (l,r) = msubst rule.defin uvars in
            if !debug_eval then
              Printf.eprintf "RULE %a → %a\n%!" print_term l print_term r;
            let rec add_n_args n t stk =
              match (n, stk) with
              | (0, stk   ) -> (t, stk)
              | (i, v::stk) -> add_n_args (i-1) (Appl(t,v)) stk
              | (_, _     ) -> assert false
            in
            let (t, stk) = add_n_args rule.arity t stk in
            if eq ~no_whnf:true ctx t l then Some(add_args r stk) else None
          in
          let ts = List.rev_map (fun r -> match_term r t stk) rs in
          let ts = from_opt_rev ts in
          if !debug_eval then
            begin
              let nb = List.length ts in
              if nb > 1 then
                Printf.eprintf (yel "(WARN) %i rules apply...\n%!") nb
            end;
          match ts with
          | []   -> add_args t stk
          | t::_ -> eval_aux ctx t []
        end
    (* In head normal form. *)
    | (t        , stk    ) -> add_args t stk
  in
  let u = eval_aux ctx t [] in
  if !debug then log "eval" "produced %a" print_term u; u

(* Equality *)
and eq : ?no_whnf:bool -> ctxt -> term -> term -> bool =
  fun ?(no_whnf=false) ctx a b ->
    if !debug then log "equa" "%a =?= %a" print_term a print_term b;
    let rec eq no_whnf a b =
      let eq_binder f g =
        let x = mkfree (new_var mkfree "_eq_binder_") in
        eq no_whnf (subst f x) (subst g x)
      in
      let trivial = if not no_whnf then eq true a b else false in
      trivial ||
      let a = if no_whnf then unfold a else eval ctx a in
      let b = if no_whnf then unfold b else eval ctx b in
      match (a,b) with
      | (Vari(x)  , Vari(y)  ) -> eq_vars x y
      | (Type     , Type     ) -> true
      | (Kind     , Kind     ) -> true
      | (Prod(a,f), Prod(b,g)) -> eq no_whnf a b && eq_binder f g
      | (Abst(a,f), Abst(b,g)) -> eq no_whnf a b && eq_binder f g
      | (Appl(t,u), Appl(f,g)) -> eq no_whnf t f && eq no_whnf u g
      | (Unif(r1) , Unif(r2) ) when r1 == r2 -> true
      | (Unif(r)  , _        ) ->
          begin
            match !r with
            | None   -> r := Some(b); true
            | Some a -> eq no_whnf a b
          end
      | (_        , Unif(r)  ) ->
          begin
            match !r with
            | None   -> r := Some(a); true
            | Some b -> eq no_whnf a b
          end
      | (_        , _        ) -> false
    in
    let res = eq no_whnf a b in
    if !debug then
      begin
        let c = if res then '=' else '/' in
        log "equa" "%a =%c= %a" print_term a c print_term b;
      end;
    res

let rec lift : term -> tbox = fun t ->
  match t with
  | Vari(x)   -> box_of_var x
  | Type      -> t_type
  | Kind      -> t_kind
  | Prod(a,b) -> t_prod (lift a) (binder_name b)
                   (fun x -> lift (subst b (mkfree x)))
  | Abst(a,t) -> t_abst (lift a) (binder_name t)
                   (fun x -> lift (subst t (mkfree x)))
  | Appl(t,u) -> t_appl (lift t) (lift u)
  | Unif(r)   -> (match !r with Some t -> lift t | None -> box t)

let bind_vari : term var -> term -> (term,term) binder = fun x t ->
  unbox (bind_var x (lift t))

(* Judgements *)
let rec infer : ctxt -> term -> term = fun ctx t ->
  let t = unfold t in
  if !debug_infer then log "infr" "type of [%a]?" print_term t;
  let a =
    match t with
    | Vari(x)   -> find x ctx
    | Type      -> Kind
    | Kind      -> raise Not_found
    | Prod(a,b) -> let x = new_var mkfree (binder_name b) in
                   let b = subst b (mkfree x) in
                   begin
                     match infer (add_var x a ctx) b with
                     | Kind -> Kind
                     | Type -> Type 
                     | _    ->
                         Printf.eprintf "Expected Type of Kind for [%a]\n%!"
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
                         if has_type ctx u a then subst b u
                         else raise Not_found
                     | _         ->
                         raise Not_found
                   end
    | Unif(_)   -> assert false
  in
  if !debug_infer then log "infr" "%a : %a" print_term t print_term a;
  let res = eval ctx a in
  if !debug_infer && res != a then log "infr" "→ %a" print_term res;
  assert (has_type ctx t res); res

and has_type : ctxt -> term -> term -> bool = fun ctx t a ->
  let t = unfold t in
  let a = unfold a in
  if !debug then
    log "type" "%a ⊢ %a : %a" print_ctxt ctx print_term t print_term a;
  let a = eval ctx a in
  match (t, a) with
  (* Sort *)
  | (Type     , Kind     ) -> true
  (* Variable *)
  | (Vari(x)  , a        ) -> eq ctx (find x ctx) a
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
  (* Unification variable. *)
  | (Unif(_)  , _        ) ->
      true (* Only for patterns. *)
  (* No rule apply. *)
  | (_        , _        ) -> false

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
  | NewVar of string * p_term
  | Rule   of string list * p_term * p_term
  | Check  of p_term * p_term
  | Infer  of p_term
  | Eval   of p_term
  | Conv   of p_term * p_term

let parser toplevel =
  | x:ident ":" a:expr                  -> NewVar(x,a)
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

let wildcards : term var list ref = ref []
let new_wildcard : unit -> tbox =
  let counter = ref (-1) in
  fun () ->
    incr counter;
    let x = new_var mkfree (Printf.sprintf "#%i#" !counter) in
    wildcards := x :: !wildcards; box_of_var x

let to_tbox : bool -> ctxt -> p_term -> tbox = fun allow_wild ctx t ->
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
    | P_Wild        ->
        if not allow_wild then
          begin
            Printf.eprintf "Wildcard \"_\" not allowd here...\n%!";
            exit 1
          end;
        new_wildcard ()
  in
  build [] t

let to_term : ctxt -> p_term -> term = fun ctx t ->
  unbox (to_tbox false ctx t)

let to_tbox_wc : ctxt -> p_term -> tbox * term var array = fun ctx t ->
  wildcards := [];
  let t = to_tbox true ctx t in
  (t, Array.of_list !wildcards)

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
        let (t, wcs) = to_tbox_wc ctx_aux t in
        let u = to_tbox false ctx_aux u in
        let xs = Array.append xs wcs in
        let defin = unbox (bind_mvar xs (box_pair t u)) in
        let t = unbox (bind_mvar wcs t) in
        let new_unif _ = Unif(ref None) in
        let t = msubst t (Array.init (Array.length wcs) new_unif) in
        let u = unbox u in
        begin
          match pattern_data t with
          | None      ->
              Printf.eprintf "Not a valid pattern...\n%!";
              exit 1
          | Some(x,i) ->
              let rule = {defin; const = x; arity = i} in
              try
                let tt = infer ctx_aux t in
                if !debug then Printf.eprintf "LEFT : %a\n%!" print_term tt;
                let tu = infer ctx_aux u in
                if !debug then Printf.eprintf "RIGHT: %a\n%!" print_term tu;
                if not (eq ctx tt tu) then raise Not_found;
                Printf.printf "(rule) %a → %a\n%!" print_term t print_term u;
                add_rule rule ctx
              with Not_found ->
                Printf.eprintf (red "Ill-typed rule [%a → %a]\n%!")
                  print_term t print_term u;
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
            Printf.eprintf (red "(chck) Type error...\n%!");
            exit 1
          end
    | Infer(t)     ->
        let t = to_term ctx t in
        begin
          try
            let a = infer ctx t in
            Printf.eprintf "(infr) %a : %a\n%!" print_term t print_term a
          with Not_found ->
            Printf.eprintf (red "(infr) %a : UNABLE TO INFER\n%!")
              print_term t
        end;
        ctx
    | Eval(t)      ->
        let t = to_term ctx t in
        let v = eval ctx t in
        Printf.eprintf "(eval) %a\n%!" print_term v;
        ctx
    | Conv(t,u)    ->
        let t = to_term ctx t in
        let u = to_term ctx u in
        begin
          if not (eq ctx t u) then
            Printf.eprintf (red "(conv) UNABLE TO CONVERT\n%!")
          else
            Printf.eprintf "(conv) OK\n%!"
        end;
        ctx
  in
  List.fold_left handle_item ctx (parse_file fname)

(* Run files *)
let _ =
  let usage = Sys.argv.(0) ^ " [--debug str] [FILE1] ... [FILEN]" in
  let spec =
    [("--debug", Arg.String set_debug, "Set debugging mode.") ]
  in
  let files = ref [] in
  let anon fn = files := fn :: !files in
  Arg.parse spec anon usage;
  let files = List.rev !files in
  List.fold_left handle_file empty_ctxt files
