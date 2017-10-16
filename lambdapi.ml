(**** Colorful error / warning messages *************************************)

(* Format transformers (colors). *)
let red fmt = "\027[31m" ^^ fmt ^^ "\027[0m%!"
let gre fmt = "\027[32m" ^^ fmt ^^ "\027[0m%!"
let yel fmt = "\027[33m" ^^ fmt ^^ "\027[0m%!"
let blu fmt = "\027[34m" ^^ fmt ^^ "\027[0m%!"
let mag fmt = "\027[35m" ^^ fmt ^^ "\027[0m%!"
let cya fmt = "\027[36m" ^^ fmt ^^ "\027[0m%!"

(* [wrn fmt] prints a yellow warning message with [Printf] format [fmt]. Note
   that the output buffer is flushed by the function. *)
let wrn : ('a, out_channel, unit) format -> 'a =
  fun fmt -> Printf.eprintf (yel fmt)

(* [err fmt] prints a red error message with [Printf] format [fmt]. Note that
   the output buffer is flushed by the function. *)
let err : ('a, out_channel, unit) format -> 'a =
  fun fmt -> Printf.eprintf (red fmt)

(* [fatal fmt] is like [err fmt], but it aborts the program with [exit 1]. *)
let fatal : ('a, out_channel, unit, unit, unit, 'b) format6 -> 'a =
  fun fmt -> Printf.kfprintf (fun _ -> exit 1) stderr (red fmt)

(**** Debugging messages management *****************************************)

(* Various debugging / message flags. *)
let quiet       = ref false
let debug       = ref false
let debug_eval  = ref false
let debug_infer = ref false
let debug_patt  = ref false

(* [debug_enabled ()] indicates whether any debugging flag is enable. *)
let debug_enabled : unit -> bool = fun () ->
  !debug || !debug_eval || !debug_infer || !debug_patt

(* [set_debug str] enables debugging flags according to [str]. *)
let set_debug : string -> unit =
  let enable c =
    match c with
    | 'a' -> debug       := true
    | 'e' -> debug_eval  := true
    | 'i' -> debug_infer := true
    | 'p' -> debug_patt  := true
    | _   -> wrn "Unknown debug flag %C\n" c
  in
  String.iter enable

(* [log name fmt] prints a message in the log with the [Printf] format [fmt].
   The message is identified with the name (or flag) [name], and coloured in
   cyan. Note that the output buffer is flushed by the function, and that a
   newline character ['\n'] is appended to the output. *)
let log : string -> ('a, out_channel, unit) format -> 'a =
  fun name fmt -> Printf.eprintf ((cya "[%s] ") ^^ fmt ^^ "\n%!") name

(* [out fmt] prints an output message with the [Printf] format [fmt]. Note
   that the output buffer is flushed by the function, and that the message is
   displayed in magenta whenever a debugging mode is enabled. *)
let out : ('a, out_channel, unit) format -> 'a =
  fun fmt ->
    let fmt = if debug_enabled () then mag fmt else fmt ^^ "%!" in
    if !quiet then Printf.ifprintf stdout fmt else Printf.printf fmt

(**** Function that should be in the standard library ***********************)

(* [from_opt_rev l] extracts the values contained in the [Some] constructors
   in a list of [option] values. The values appear in reverse order in the
   produced list. *)
let from_opt_rev : 'a option list -> 'a list = fun l ->
  let rec aux acc l =
    match l with
    | []          -> acc
    | None   :: l -> aux acc l
    | Some e :: l -> aux (e::acc) l
  in aux [] l

(**** Abstract syntax of the language ***************************************)

(* Type of terms (and types). *)
type term =
  (* Free variable. *)
  | Vari of term Bindlib.var
  (* "Type" constant. *)
  | Type
  (* "Kind" constant. *)
  | Kind
  (* Symbol (static or definable). *)
  | Symb of symbol
  (* Dependent product. *)
  | Prod of term * (term, term) Bindlib.binder
  (* Abstraction. *)
  | Abst of term * (term, term) Bindlib.binder
  (* Application. *)
  | Appl of term * term
  (* Unification variable. *)
  | Unif of term option ref

(* Representation of a reduction rule. The [arity] is the minimal number of
   arguments that are required for the rule to apply. The definition [defin]
   binds the context of the rule to its LHS and RHS. *)
and rule =
  { defin : (term, term * term) Bindlib.mbinder
  ; arity : int }

(* NOTE: to check if a rule [r] can be applied on a term [t] using the above
   representation is really easy. First, one should substitute the [r.defin]
   binder (with the [Bindlib.msubst] function) using an array of unification
   variables (of size [Bindlib.mbinder_arity r.defin]) to obtain a couple of
   two terms [(lhs, rhs)]. To check if [r] applies, one should test equality
   (with unification) between [t] and [lhs]. If they are equal then the rule
   applies and the result of the application is exactly [rhs], otherwise the
   rule does not apply. *)

(**** Symbols (static or definable) *****************************************)

(* Representation of a static symbol. *)
and sym =
  { sym_name  : string
  ; sym_type  : term
  ; sym_path  : string list }

(* Representation of a definable symbol. Note that it carries its reduction
   rules in a reference, that should be updated when new rules are added. *)
and def =
  { def_name  : string
  ; def_type  : term
  ; def_rules : rule list ref
  ; def_path  : string list }

(* NOTE: the [path] stored in a symbol corresponds to its "module path". In
   the current implementation, the module path [["dira"; "dirb"; "file"]]
   corresponds to the file ["dira/dirb/file.lp"]. It is printed and read in
   the source code as ["dira::dirb::file"] *)

(* Representation of a (static or definable) symbol. *)
and symbol =
  | Sym of sym
  | Def of def

(* [symbol_type s] returns the type of the given symbol [s]. *)
let symbol_type : symbol -> term =
  fun s ->
    match s with
    | Sym(sym) -> sym.sym_type
    | Def(def) -> def.def_type

(* [symbol_name s] returns the full name of the given symbol [s] (including
   the module path). *)
let symbol_name : symbol -> string = fun s ->
  let (path, name) =
    match s with
    | Sym(sym) -> (sym.sym_path, sym.sym_name)
    | Def(def) -> (def.def_path, def.def_name)
  in
  String.concat "::" (path @ [name])

(**** Signature *************************************************************)

module Sign =
  struct
    type t =
      { syms  : (string, sym) Hashtbl.t
      ; defs  : (string, def) Hashtbl.t
      ; path  : string list }
 
    let create : string list -> t = fun path ->
      let syms  = Hashtbl.create 37 in
      let defs  = Hashtbl.create 37 in
      { syms ; defs ; path }

    let name_exists : string -> t -> bool = fun n sign ->
      Hashtbl.mem sign.syms n || Hashtbl.mem sign.defs n

    let new_sym : t -> string -> term -> unit = fun sign sym_name sym_type ->
      if name_exists sym_name sign then wrn "Redefinition of %s.\n" sym_name;
      let sym =
        { sym_name ; sym_type ; sym_path = sign.path }
      in
      Hashtbl.add sign.syms sym_name sym
 
    let new_def : t -> string -> term -> unit = fun sign def_name def_type ->
      if name_exists def_name sign then wrn "Redefinition of %s.\n" def_name;
      let def =
        { def_name ; def_type ; def_rules = ref [] ; def_path = sign.path }
      in
      Hashtbl.add sign.defs def_name def
 
    let find_symbol : t -> string -> symbol = fun sign name ->
      try Sym (Hashtbl.find sign.syms name)
      with Not_found -> Def (Hashtbl.find sign.defs name)
  end

(**** Smart constructors and other Bindlib-related things *******************)

open Bindlib

type tbox = term bindbox
type tvar = term var

let mkfree : tvar -> term =
  fun x -> Vari(x)

let t_type : tbox =
  box Type

let t_kind : tbox =
  box Kind

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
type 'a eq = 'a -> 'a -> bool
let eq_binder : term eq -> (term, term) Bindlib.binder eq =
  fun eq f g -> f == g ||
    let x = mkfree (new_var mkfree "_eq_binder_") in
    eq (subst f x) (subst g x)

(* Unfolding of unification variables. *)
let rec unfold : term -> term = fun t ->
  match t with
  | Unif(r) -> (match !r with Some(t) -> unfold t | None -> t) 
  | _       -> t

(* Separate the head term and its arguments. *)
let get_args : term -> term * term list = fun t ->
  let rec get acc t =
    match unfold t with
    | Appl(t,u) -> get (u::acc) t
    | t         -> (t, acc)
  in
  get [] t

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
 
(* Check that the given term is a pattern and returns its data. *)
let pattern_data : term -> def * int = fun t ->
  let (hd, args) = get_args t in
  match unfold hd with
  | Symb(Def(s)) -> (s, List.length args)
  | Symb(Sym(s)) -> fatal "%s is not a definable symbol...\n" s.sym_name
  | _            -> fatal "%a is not a valid pattern...\n" print_term t

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
          if !debug_eval then
            begin
              let nb = List.length ts in
              if nb > 1 then wrn "%i rules apply...\n%!" nb
            end;
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

type constrs = (term * term) list

let constraints = ref None
let add_constraint : Sign.t -> term -> term -> bool = fun sign a b ->
  match !constraints with
  | None    -> false
  | Some cs -> let c = (eval sign a, eval sign b) in
               constraints := Some (c :: cs); true

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
                     Prod(a, unbox (bind_var x (lift b)))
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
  a

and has_type : Sign.t -> ctxt -> term -> term -> bool = fun sign ctx t a ->
  let eq_modulo sg a b =
    eq_modulo sg a b || add_constraint sg a b
  in
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

let infer_with_constrs : Sign.t -> ctxt -> term -> term * constrs =
  fun sign ctx t ->
    constraints := Some [];
    let a = infer sign ctx t in
    let cnstrs = match !constraints with Some cs -> cs | None -> [] in
    constraints := None;
    if !debug_patt then
      begin
        log "patt" "inferred type [%a] for [%a]" print_term a print_term t;
        let fn (x,a) =
          log "patt" "  with\t%s\t: %a" (name_of x) print_term a
        in
        List.iter fn ctx;
        let fn (a,b) =
          log "patt" "  where\t%a == %a" print_term a print_term b
        in
        List.iter fn cnstrs
      end;
    (a, cnstrs)

let sub_from_constrs : constrs -> tvar array * term array = fun cs ->
  let rec build_sub acc cs =
    match cs with
    | []        -> acc
    | (a,b)::cs ->
        let (ha,argsa) = get_args a in
        let (hb,argsb) = get_args b in
        match (unfold ha, unfold hb) with
        | (Symb(Sym(sa)), Symb(Sym(sb))) when sa == sb ->
            let cs =
              try List.combine argsa argsb @ cs with Invalid_argument _ -> cs
            in
            build_sub acc cs
        | (Symb(Def(sa)), Symb(Def(sb))) when sa == sb ->
            wrn "%s may not be injective...\n%!" sa.def_name;
            build_sub acc cs
        | (Vari(x)      , _            ) when argsa = [] ->
            build_sub ((x,b)::acc) cs
        | (_            , Vari(x)      ) when argsb = [] ->
            build_sub ((x,a)::acc) cs
        | (a            , b            ) ->
            wrn "Not implemented [%a] [%a]...\n%!" print_term a print_term b;
            build_sub acc cs
  in
  let sub = build_sub [] cs in
  (Array.of_list (List.map fst sub), Array.of_list (List.map snd sub))

let eq_modulo_constrs : constrs -> Sign.t -> term -> term -> bool =
  fun constrs sign a b -> eq_modulo sign a b ||
    let (xs,sub) = sub_from_constrs constrs in
    let p = unbox (bind_mvar xs (box_pair (lift a) (lift b))) in
    let (a,b) = msubst p sub in
    eq_modulo sign a b

(* Parser *)
type p_term =
  | P_Vari of string list * string
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
  | fs:{ident "::"}* x:ident
      when p = `Atom
      -> P_Vari(fs,x)
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

let wildcards : term var list ref = ref []
let wildcard_counter = ref (-1)
let new_wildcard : unit -> tbox = fun () ->
  incr wildcard_counter;
  let x = new_var mkfree (Printf.sprintf "#%i#" !wildcard_counter) in
  wildcards := x :: !wildcards; box_of_var x

type env = (string * tvar) list

let loaded : (string list, Sign.t) Hashtbl.t = Hashtbl.create 7

let compile_ref : (bool -> string -> Sign.t) ref =
  ref (fun _ _ -> assert false)

let load_signature : string list -> Sign.t = fun fs ->
  try Hashtbl.find loaded fs with Not_found ->
  let file = (String.concat "/" fs) ^ ".lp" in
  !compile_ref false file

let to_tbox : bool -> env -> Sign.t -> p_term -> tbox =
  fun allow_wild vars sign t ->
    let rec build vars t =
      match t with
      | P_Vari([],x)  ->
          begin
            try box_of_var (List.assoc x vars) with Not_found ->
            try t_symb sign x with Not_found ->
            fatal "Unbound variable %S...\n%!" x
          end
      | P_Vari(fs,x)  ->
          begin
            let sign = load_signature fs in
            try t_symb sign x with Not_found ->
              let x = String.concat "::" (fs @ [x]) in
              fatal "Unbound symbol %S...\n%!" x
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
          if not allow_wild then fatal "\"_\" not allowed in terms...\n";
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
          fatal "%s is neither of type Type nor Kind.\n" x
        in
        let kind = if d then "defi" else "symb" in
        out "(%s) %s : %a (of sort %s)\n" kind x print_term a sort;
        if d then Sign.new_def sign x a else Sign.new_sym sign x a
    | Rule(xs,t,u) ->
        (* Scoping the LHS and RHS. *)
        let vars = List.map (fun x -> (x, new_var mkfree x)) xs in
        let (t, wcs) = to_tbox_wc ~vars sign t in
        let u = to_tbox false vars sign u in
        (* Building the definition. *)
        let xs = Array.append (Array.of_list (List.map snd vars)) wcs in
        let defin = unbox (bind_mvar xs (box_pair t u)) in
        (* Constructing the typing context and the terms. *)
        let xs = Array.to_list xs in
        let ctx = List.map (fun x -> (x, Unif(ref None))) xs in
        let t = unbox t in
        let u = unbox u in
        (* Check that the LHS is a pattern and build the rule. *)
        let (s,i) = pattern_data t in
        let rule = { defin ; arity = i } in
        (* Infer the type of the LHS and the constraints. *)
        let (tt, tt_constrs) =
          try infer_with_constrs sign ctx t with Not_found ->
            fatal "Unable to infer the type of [%a]\n" print_term t
        in
        (* Infer the type of the RHS and the constraints. *)
        let (tu, tu_constrs) =
          try infer_with_constrs sign ctx u with Not_found ->
            fatal "Unable to infer the type of [%a]\n" print_term u
        in
        (* Checking the implication of constraints. *)
        let check_constraint (a,b) =
          if not (eq_modulo_constrs tt_constrs sign a b) then
            fatal "A constraint is not satisfied...\n"
        in
        List.iter check_constraint tu_constrs;
        (* Checking if the rule is well-typed. *)
        if eq_modulo_constrs tt_constrs sign tt tu then
          begin
            out "(rule) %a → %a\n" print_term t print_term u;
            s.def_rules := !(s.def_rules) @ [rule]
          end
        else
          begin
            err "Infered type for LHS: %a\n" print_term tt;
            err "Infered type for RHS: %a\n" print_term tu;
            fatal "[%a → %a] is ill-typed\n" print_term t print_term u
          end
    | Check(t,a)   ->
        let t = to_term sign t in
        let a = to_term sign a in
        if has_type sign empty_ctxt t a then
          out "(chck) %a : %a\n" print_term t print_term a
        else
          fatal "%a does not have type %a...\n" print_term t print_term a
    | Infer(t)     ->
        let t = to_term sign t in
        begin
          try
            let a = infer sign empty_ctxt t in
            out "(infr) %a : %a\n" print_term t print_term a
          with Not_found ->
            err "%a : unable to infer\n%!" print_term t
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

let obj_file : string -> string = fun file ->
  Filename.chop_extension file ^ ".lpo"

let module_path : string -> string list = fun file ->
  let base = Filename.chop_extension (Filename.basename file) in
  let dir  = Filename.dirname  file in
  let rec build_path acc dir =
    let dirbase = Filename.basename dir in
    let dirdir  = Filename.dirname  dir in
    if dirbase = "." then acc else build_path (dirbase::acc) dirdir
  in
  build_path [base] dir

let mod_time : string -> float = fun fname ->
  if Sys.file_exists fname then Unix.((stat fname).st_mtime)
  else neg_infinity

let binary_time : float = mod_time "/proc/self/exe"

let more_recent source target =
  mod_time source > mod_time target
  || binary_time > mod_time target

let compile : bool -> string -> Sign.t = fun force file ->
  if not (Sys.file_exists file) then fatal "File not found: %s\n" file;
  let obj = obj_file file in
  let fs = module_path file in
  if more_recent file obj || (force && not (Hashtbl.mem loaded fs)) then
    begin
      out "Loading file [%s]\n%!" file;
      let sign = Sign.create fs in
      begin
        try handle_file sign file with e ->
          fatal "Uncaught exception...\n%s\n%!" (Printexc.to_string e)
      end;
      let oc = open_out obj in
      Marshal.to_channel oc sign [Marshal.Closures];
      close_out oc;
      Hashtbl.add loaded fs sign;
      out "Done with file [%s]\n%!" file;
      sign
    end
  else
    try Hashtbl.find loaded fs with Not_found ->
    let ic = open_in obj in
    let sign = Marshal.from_channel ic in
    close_in ic;
    Hashtbl.add loaded fs sign; sign

let _ = compile_ref := compile

let compile force file = ignore (compile force file)

(* Run files *)
let _ =
  let usage = Sys.argv.(0) ^ " [--debug [a|e|i|p]] [--quiet] [FILE] ..." in
  let flags =
    [ "a : general debug informations"
    ; "e : extra debugging informations for equality"
    ; "i : extra debugging informations for inference"
    ; "p : extra debugging informations for patterns" ]
  in
  let flags = List.map (fun s -> String.make 18 ' ' ^ s) flags in
  let flags = String.concat "\n" flags in
  let spec =
    [ ("--debug", Arg.String set_debug, "<str> Set debugging mode:\n" ^ flags)
    ; ("--quiet", Arg.Set quiet       , " Disable output") ]
  in
  let files = ref [] in
  let anon fn = files := fn :: !files in
  Arg.parse (Arg.align spec) anon usage;
  List.iter (compile true) (List.rev !files)
