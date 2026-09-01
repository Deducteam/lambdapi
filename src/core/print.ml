(** Pretty-printing for the core AST.

    The functions of this module are used for printing terms and other objects
    defined in the {!module:Term} module.  This is mainly used for displaying
    log messages, and feedback in case of success or error while type-checking
    terms or testing convertibility. *)

open Lplib open Base open Extra
open Timed
open Common open Debug open Name
open Term
open Sig_state

(** Logging function for printing. *)
let log = Logger.make 'p' "prnt" "pretty-printing"
let log = log.pp

(*****************************************************************************
printing flags
*****************************************************************************)

(** Current signature state. *)
let sig_state : sig_state ref = ref Sig_state.dummy

(** Flag for printing the domains of λ-abstractions. *)
let print_domains : bool ref = Console.register_flag "print_domains" false

(** Flag for printing implicit arguments. *)
let print_implicits : bool ref = Console.register_flag "print_implicits" false

(** Flag for printing contexts in unification problems. *)
let print_contexts : bool ref = Console.register_flag "print_contexts" false

(** Flag for printing metavariable arguments. *)
let print_meta_args : bool ref = Console.register_flag "print_meta_args" false

let print_pattern_names : bool ref = ref true

let print_implicits_and_domains_in f x =
  let i = !print_implicits
  and d = !print_domains
  and p = !print_pattern_names in
  print_implicits := true;
  print_domains := true;
  print_pattern_names := false;
  try
    let r = f x in
    print_implicits := i;
    print_domains := d;
    print_pattern_names := p;
    r
  with e ->
    print_implicits := i;
    print_domains := d;
    print_pattern_names := p;
    raise e

(*****************************************************************************
printing functions
*****************************************************************************)

(*let get_safe_prefix s idmap =
  let s',idmap' = get_safe_prefix s idmap in
  log "get_safe_prefix(%S,%a) = (%S,%a)"
    s (D.strmap D.int) idmap s' (D.strmap D.int) idmap';
  s',idmap'*)

let safe_unbind_no_check (idmap:int StrMap.t) (b:binder)
    : (var * term) * int StrMap.t =
  let name, idmap = get_safe_prefix (binder_name b) idmap in
  unbind ~name b, idmap

let safe_unbind (idmap:int StrMap.t) (b:binder): (var * term) * int StrMap.t =
  if binder_occur b then safe_unbind_no_check idmap b else unbind b, idmap

let assoc : Pratter.associativity pp = fun ppf assoc ->
  match assoc with
  | Neither -> ()
  | Left -> out ppf " left"
  | Right -> out ppf " right"

let notation : 'a pp -> 'a notation pp = fun elt ->
  let rec notation ppf = function
  | Prefix(p) -> out ppf "prefix %a" elt p
  | Infix(a,p) -> out ppf "infix%a %a" assoc a elt p
  | Postfix(p) -> out ppf "postfix %a" elt p
  | Succ n -> notation ppf n
  | Quant -> out ppf "quantifier"
  | _ -> ()
  in notation

let uid : string pp = string

let prop : prop pp = fun ppf p ->
  match p with
  | AC true -> out ppf "left associative commutative "
  | AC false -> out ppf "associative commutative "
  | Assoc true -> out ppf "left associative "
  | Assoc false -> out ppf "associative "
  | Const -> out ppf "constant "
  | Commu -> out ppf "commutative "
  | Defin -> ()
  | Injec -> out ppf "injective "

let expo : expo pp = fun ppf e ->
  match e with
  | Privat -> out ppf "private "
  | Protec -> out ppf "protected "
  | Public -> ()

let match_strat : match_strat pp = fun ppf s ->
  match s with
  | Eager -> ()
  | Sequen -> out ppf "sequential "

let do_not_qualify = ref false

let no_qualif f =
 let saved = !do_not_qualify in
 do_not_qualify := true ;
 let res = f () in
 do_not_qualify := saved ;
 res

let sym : sym pp = fun ppf s ->
  if !print_implicits && s.sym_impl <> [] then out ppf "@";
  let ss = !sig_state and n = s.sym_name and p = s.sym_path in
  if !do_not_qualify || Path.Set.mem p ss.open_paths then uid ppf n
  else
    match Path.Map.find_opt p ss.path_alias with
    | None ->
      (* Do not print path of temporary symbols introduced in sr.ml. *)
      if n <> "" && n.[0] = LibTerm.sym_meta_prefix then uid ppf n
      else qsym ppf s
    | Some alias -> out ppf "%a.%a" uid alias uid n

let var : var pp = fun ppf x -> uid ppf (base_name x)

(** Exception raised when trying to convert a term into a nat. *)
exception Not_a_nat

let builtin name =
  try StrMap.find name (!sig_state).builtins with Not_found -> raise Not_a_nat

(** [nat_of_term t] converts a term into a natural number.
    @raise Not_a_nat if this is not possible. *)
let nat_of_term : term -> int = fun t ->
  let zero = builtin "nat_zero" and succ = builtin "nat_succ" in
  let rec nat acc = fun t ->
    match get_args t with
    | (Symb s, [u]) when s == succ -> nat (acc+1) u
    | (Symb s,  []) when s == zero -> acc
    | _ -> raise Not_a_nat
  in nat 0 t

(** [pos_of_term t] converts a term into a positive number.
    @raise Not_a_nat if this is not possible. *)
let pos_of_term : term -> int = fun t ->
  let one = builtin "pos_one" and dbl = builtin "pos_double"
  and suc_dbl = builtin "pos_succ_double" in
  let rec pos = fun t ->
    match get_args t with
    | (Symb s, [u]) when s == dbl -> 2 * (pos u)
    | (Symb s, [u]) when s == suc_dbl -> (2 * pos u) + 1
    | (Symb s,  []) when s == one -> 1
    | _ -> raise Not_a_nat
  in pos t

(** [int_of_term t] converts a term into a positive number.
    @raise Not_a_nat if this is not possible. *)
let int_of_term : term -> int = fun t ->
  let zero = builtin "int_zero" and pos = builtin "int_positive"
  and neg = builtin "int_negative" in
  match get_args t with
  | (Symb s, [u]) when s == pos -> pos_of_term u
  | (Symb s, [u]) when s == neg -> - (pos_of_term u)
  | (Symb s,  []) when s == zero -> 0
  | _ -> raise Not_a_nat

(** [are_quant_args args] returns [true] iff [args] has only one argument
   that is an abstraction. *)
let are_quant_args : term list -> bool = fun args ->
  match args with
  | [b] -> is_abst b
  | _ -> false

let rec wrap idmap ppf t =
  match unfold t with
  | Abst _ | LLet _ | Appl _ -> out ppf "(%a)" (term_in idmap) t
  | Prod(_,b) when binder_occur b -> out ppf "(%a)" (term_in idmap) t
  | _ -> term_in idmap ppf t

and appl idmap ppf h ts =
  match ts with
  | [] -> head idmap ppf h
  | _ -> wrap idmap ppf h; List.iter (out ppf " %a" (wrap idmap)) ts

and postfix idmap ppf s args =
  match args with
  | [] -> out ppf "(%a)" sym s
  | [t] -> out ppf "%a %a" (wrap idmap) t sym s
  | t::ts ->
    out ppf "(%a %a)" (wrap idmap) t sym s;
    List.iter (out ppf " %a" (wrap idmap)) ts

and term_in idmap ppf t =
  let h,ts = get_args t in
  match h with
  | Symb s ->
    if !print_implicits && s.sym_impl <> [] then appl idmap ppf h ts
    else
      let ts = LibTerm.remove_impl_args s ts in
      let number f t =
        try out ppf "%i" (f t) with Not_a_nat -> appl idmap ppf h ts in
      begin match !(s.sym_nota) with
        | Quant when are_quant_args ts -> quantifier idmap ppf s ts
        | Postfix _ -> postfix idmap ppf s ts
        | Infix _ ->
          begin
            match ts with
            | [] -> out ppf "(%a)" sym s
            | [t] -> out ppf "(%a) %a" sym s (wrap idmap) t
            | [l;r] ->
              if s.sym_path = Sign.Ghost.path then
                out ppf "%a %a %a" (term_in idmap) l sym s (term_in idmap) r
              else out ppf "%a %a %a" (wrap idmap) l sym s (wrap idmap) r
            | l::r::ts ->
              out ppf "(%a %a %a)" (wrap idmap) l sym s (wrap idmap) r;
              List.iter (out ppf " %a" (wrap idmap)) ts
          end
        | Zero | IntZero -> out ppf "0"
        | Succ (Postfix _) ->
          (try out ppf "%i" (nat_of_term t)
           with Not_a_nat -> postfix idmap ppf s ts)
        | Succ _ -> number nat_of_term t
        | PosOne -> out ppf "1"
        | PosDouble | PosSuccDouble -> number pos_of_term t
        | IntPos | IntNeg -> number int_of_term t
        | _ -> appl idmap ppf h ts
      end
  | _ -> appl idmap ppf h ts

and quantifier idmap ppf s ts =
  match ts with
  | [b] ->
    begin
      match unfold b with
      | Abst(a,b) ->
        let (x,p),idmap' = safe_unbind idmap b in
        out ppf "%a %a%a, %a" sym s var x (typ_in idmap) a (term_in idmap') p
      | _ -> assert false
    end
  | _ -> assert false

and meta ppf m = out ppf "?%d" m.meta_key

and env idmap ppf ts =
  if Array.length ts > 0 then
    out ppf ".[%a]" (Array.pp (term_in idmap) ";") ts

and head idmap ppf t =
  match unfold t with
  | Appl _ -> assert false
  | Wild -> out ppf "_"
  | TRef r ->
    (match !r with None -> out ppf "<TRef>" | Some t -> term_in idmap ppf t)
  | Vari x -> var ppf x
  | Type -> out ppf "TYPE"
  | Kind -> out ppf "KIND"
  | Symb s -> sym ppf s
  | Meta(m,e) ->
    meta ppf m; if !print_meta_args then env idmap ppf e
  | Plac _ -> out ppf "_"
  | Patt(None,_,_) -> assert false
  | Patt(Some i,n,e) ->
    if !print_pattern_names && n<>"" then out ppf "$%s%a" n (env idmap) e
    else out ppf "$%d%a" i (env idmap) e
  | Bvar _ -> assert false
  | Abst(a,b)   ->
    if binder_occur b then
      begin
        let (x,t),idmap' = safe_unbind_no_check idmap b in
        out ppf "λ %a" var x;
        if !print_domains then
          out ppf ":%a, %a" (term_in idmap) a (term_in idmap') t
        else abstractions idmap' ppf t
      end
    else
      begin
        let _,t = unbind b in
        out ppf "λ _";
        if !print_domains then
          out ppf ":%a, %a" (term_in idmap) a (term_in idmap) t
        else abstractions idmap ppf t
      end
  | Prod(a,b) ->
    if binder_occur b then
      let (x,t),idmap' = safe_unbind_no_check idmap b in
      out ppf "Π %a:%a, %a" var x (term_in idmap) a (term_in idmap') t
    else
      let _,t = unbind b in
      out ppf "%a → %a" (wrap idmap) a (term_in idmap) t
  | LLet(a,t,b) ->
    out ppf "let ";
    if binder_occur b then
      begin
        let (x,u),idmap' = safe_unbind_no_check idmap b in
        out ppf "%a%a ≔ %a in %a"
          var x (typ_in idmap) a (term_in idmap) t (term_in idmap') u
      end
    else
      begin
        let _,u = unbind b in
        out ppf "_%a ≔ %a in %a"
          (typ_in idmap) a (term_in idmap) t (term_in idmap) u
      end

and abstractions idmap ppf t =
  match unfold t with
  | Abst(_,b) ->
    if binder_occur b then
      let (x,t),idmap' = safe_unbind_no_check idmap b in
      out ppf " %a%a" var x (abstractions idmap') t
    else let _,t = unbind b in out ppf " _%a" (abstractions idmap) t
  | t -> out ppf ", %a" (term_in idmap) t

and typ_in idmap ppf a =
  if !print_domains then out ppf ":%a" (term_in idmap) a

let term_in idmap ppf t =
  let idmap =
    StrMap.fold (fun n _ -> Name.add_name n) !sig_state.in_scope idmap in
  let s = Logger.get_activated_loggers() in
  if String.contains s 'p' then term_in idmap ppf t
  else
    begin
      Logger.reset_loggers ~default:"" ();
      try term_in idmap ppf t; Logger.reset_loggers ~default:s ()
      with e -> Logger.reset_loggers ~default:s (); raise e
    end

let term = term_in StrMap.empty

let env = env StrMap.empty

let rec prod_in : int StrMap.t -> (term * bool list) pp =
  let decl idmap ppf (x,t) = out ppf "%a:%a" var x (wrap idmap) t in
  let decl i idmap ppf d =
    if i then out ppf "[%a]" (decl idmap) d else decl idmap ppf d in
  fun idmap ppf (t,impl) ->
  match unfold t, impl with
  | Prod(a,b), i::impl ->
    if binder_occur b then
      let (x,t),idmap' = safe_unbind_no_check idmap b in
      out ppf "Π %a, %a" (decl i idmap) (x,a) (prod_in idmap') (t,impl)
    else
      let x,t = unbind ~name:"_" b in
      out ppf "Π %a, %a" (decl i idmap) (x,a) (prod_in idmap) (t,impl)
  | _ -> term_in idmap ppf t

let prod = prod_in StrMap.empty

let sym_type ppf s = prod ppf (!(s.sym_type), s.sym_impl)

let sym_rule : sym_rule pp = fun ppf r ->
  out ppf "%a ↪ %a" term (lhs r) term (rhs r)

let rule_of : sym -> rule pp = fun s ppf r -> sym_rule ppf (s,r)

let unif_rule : rule pp = rule_of Unif_rule.equiv

let rules_of : sym pp = fun ppf s -> D.list (rule_of s) ppf !(s.sym_rules)

(* for debug only *)

let typ = typ_in StrMap.empty

let ctxt : ctxt pp =
  let def ppf t = out ppf " ≔ %a" term t in
  let decl ppf (x,a,t) = out ppf "%a%a%a" var x typ a (Option.pp def) t in
  fun ppf c -> List.pp decl ", " ppf (List.rev c)

let typing : constr pp = fun ppf (c,t,u) ->
  if !print_contexts then out ppf "%a%s⊢ " ctxt c (if c=[] then "" else " ");
  out ppf "%a : %a" term t term u

let constr : constr pp = fun ppf (c,t,u) ->
  if !print_contexts then out ppf "%a%s⊢ " ctxt c (if c=[] then "" else " ");
  out ppf "%a ≡ %a" term t term u

let constrs : constr list pp = fun ppf cs ->
  let pp_sep ppf () = out ppf "\n       ;" in
  Format.pp_print_list ~pp_sep constr ppf cs

let metaset : MetaSet.t pp =
  let meta ppf m = out ppf "?%d:%a" m.meta_key term !(m.meta_type) in
  let pp_sep ppf () = out ppf "\n       ," in
  fun ppf set ->
  Format.pp_print_list ~pp_sep meta ppf (List.rev (MetaSet.elements set))

let problem : problem pp =
  let s = "\n       " in
  fun ppf p ->
  out ppf
    "{recompute=%b;%smetas={%a};%sto_solve={%a};%sunsolved={%a}}"
    !p.recompute s metaset !p.metas s constrs !p.to_solve s
    constrs !p.unsolved
