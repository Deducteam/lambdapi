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

(** Flag for printing the type of uninstanciated metavariables. Remark: this
   does not generate parsable terms; use for debug only. *)
let print_meta_types : bool ref =
  Console.register_flag "print_meta_types" false

(** Flag for printing contexts in unification problems. *)
let print_contexts : bool ref = Console.register_flag "print_contexts" false

(** Flag for printing metavariable arguments. *)
let print_meta_args : bool ref = Console.register_flag "print_meta_args" false

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

let path : Path.t pp = Path.pp

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
        (* Hack for printing symbols replacing metavariables in infer.ml
           unqualified. *)
        if n <> "" && let c = n.[0] in c = '$' || c = '?' then uid ppf n
        else out ppf "%a.%a" path p uid n
    | Some alias -> out ppf "%a.%a" uid alias uid n

let var : var pp = fun ppf x -> uid ppf (base_name x)

let meta : meta pp = fun ppf m -> out ppf "?%d" m.meta_key

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

(** The possible priority levels are [`Func] (top level, including abstraction
   and product), [`Appl] (application) and [`Atom] (smallest priority). *)
type priority = [`Func | `Appl | `Atom]

let rec pp p idmap ppf t =
  if Logger.log_enabled() then log "%a %a" (D.strmap D.int) idmap Raw.term t;
  let (h, args) = get_args t in
  (* standard application *)
  let pp_appl h args =
    match args with
    | []   -> head idmap (p <> `Func) ppf h
    | args ->
        if p = `Atom then out ppf "(";
        head idmap true ppf h;
        List.iter (out ppf " %a" (atom idmap)) args;
        if p = `Atom then out ppf ")"
  in
  (* postfix symbol application *)
  let postfix h s args =
    match args with
    | l::args ->
        (* Can be improved by looking at symbol priority. *)
        if p <> `Func then out ppf "(";
        if args = []
        then out ppf "%a %a" (appl idmap) l sym s
        else out ppf "(%a %a)" (appl idmap) l sym s;
        List.iter (out ppf " %a" (appl idmap)) args;
        if p <> `Func then out ppf ")"
    | [] ->
        out ppf "("; head idmap true ppf h; out ppf ")"
  in
  match h with
  | Symb(s) ->
      if !print_implicits && s.sym_impl <> [] then pp_appl h args
      else
        let number f t =
          try out ppf "%i" (f t) with Not_a_nat -> pp_appl h args in
        let args = LibTerm.remove_impl_args s args in
        begin match !(s.sym_nota) with
        | Quant when are_quant_args args ->
            if p <> `Func then out ppf "(";
            quantifier idmap ppf s args;
            if p <> `Func then out ppf ")"
        | Postfix _ -> postfix h s args
        | Infix _ ->
            begin
              match args with
              | l::r::args ->
                  if p <> `Func then out ppf "(";
                  (* Can be improved by looking at symbol priority. *)
                  if args = []
                  then out ppf "%a %a %a"
                         (appl idmap) l sym s (appl idmap) r
                  else out ppf "(%a %a %a)"
                         (appl idmap) l sym s (appl idmap) r;
                  List.iter (out ppf " %a" (appl idmap)) args;
                  if p <> `Func then out ppf ")"
              | [] ->
                  out ppf "("; head idmap true ppf h; out ppf ")"
              | _ ->
                  if p = `Atom then out ppf "(";
                  out ppf "("; head idmap true ppf h; out ppf ")";
                  List.iter (out ppf " %a" (atom idmap)) args;
                  if p = `Atom then out ppf ")"
            end
        | Zero | IntZero -> out ppf "0"
        | Succ (Postfix _) ->
            (try out ppf "%i" (nat_of_term t)
             with Not_a_nat -> postfix h s args)
        | Succ _ -> number nat_of_term t
        | PosOne -> out ppf "1"
        | PosDouble | PosSuccDouble -> number pos_of_term t
        | IntPos | IntNeg -> number int_of_term t
        | _ -> pp_appl h args
        end
  | _ -> pp_appl h args

and quantifier idmap ppf s args =
  (* assume [are_quant_args s args = true] *)
  match args with
  | [b] ->
      begin
        match unfold b with
        | Abst(a,b) ->
            let (x,p),idmap' = safe_unbind idmap b in
            out ppf "`%a %a%a, %a"
              sym s var x (typ_in idmap) a (func idmap') p
        | _ -> assert false
      end
  | _ -> assert false

and head idmap wrap ppf t =
  let env ppf ts =
    if Array.length ts > 0 then
      out ppf ".[%a]" (Array.pp (func idmap) ";") ts
  in
  match unfold t with
  | Appl(_,_)   -> assert false
  (* Application is handled separately, unreachable. *)
  | Wild        -> out ppf "_"
  | TRef(r)     ->
      (match !r with
       | None -> out ppf "<TRef>"
       | Some t -> atom idmap ppf t)
  (* Atoms are printed inconditonally. *)
  | Vari(x)     -> var ppf x
  | Type        -> out ppf "TYPE"
  | Kind        -> out ppf "KIND"
  | Symb(s)     -> sym ppf s
  | Meta(m,e)   ->
      if !print_meta_types then
        out ppf "(?%d:%a)" m.meta_key (func idmap) !(m.meta_type)
      else out ppf "?%d" m.meta_key;
      if !print_meta_args then env ppf e
  | Plac(_)     -> out ppf "_"
  | Patt(_,n,e) -> out ppf "$%a%a" uid n env e
  | Bvar _      -> assert false
  (* Product and abstraction (only them can be wrapped). *)
  | Abst(a,b)   ->
      if wrap then out ppf "(";
      if binder_occur b then
        begin
          let (x,t),idmap' = safe_unbind_no_check idmap b in
          out ppf "λ %a" var x;
          if !print_domains then
            out ppf ": %a, %a" (func idmap) a (func idmap') t
          else abstractions idmap' ppf t
        end
      else
        begin
          let _,t = unbind b in
          out ppf "λ _";
          if !print_domains then
            out ppf ": %a, %a" (func idmap) a (func idmap) t
          else abstractions idmap ppf t
        end;
      if wrap then out ppf ")"
  | Prod(a,b)   ->
      if wrap then out ppf "(";
      if binder_occur b then
        let (x,t),idmap' = safe_unbind_no_check idmap b in
        out ppf "Π %a: %a, %a" var x (appl idmap) a (func idmap') t
      else
        begin
          let _,t = unbind b in
          out ppf "%a → %a" (appl idmap) a (func idmap) t
        end;
      if wrap then out ppf ")"
  | LLet(a,t,b) ->
      if wrap then out ppf "(";
      out ppf "let ";
      if binder_occur b then
        begin
          let (x,u),idmap' = safe_unbind_no_check idmap b in
          var ppf x;
          if !print_domains then out ppf ": %a" (atom idmap) a;
            out ppf " ≔ %a in %a" (func idmap) t (func idmap') u
        end
      else
        begin
          let _,u = unbind b in
          out ppf "_";
          if !print_domains then out ppf ": %a" (atom idmap) a;
          out ppf " ≔ %a in %a" (func idmap) t (func idmap) u
        end;
      if wrap then out ppf ")"
and abstractions idmap ppf t =
  match unfold t with
  | Abst(_,b) ->
      if binder_occur b then
        let (x,t),idmap' = safe_unbind_no_check idmap b in
        out ppf " %a%a" var x (abstractions idmap') t
      else
        let _,t = unbind b in out ppf " _%a" (abstractions idmap) t
  | t -> out ppf ", %a" (func idmap) t

and typ_in : int StrMap.t -> term pp = fun idmap ppf a ->
  if !print_domains then out ppf ": %a" (func idmap) a

and atom idmap ppf t = pp `Atom idmap ppf t
and appl idmap ppf t = pp `Appl idmap ppf t
and func idmap ppf t = pp `Func idmap ppf t

let term_in = func

let term = term_in StrMap.empty

let rec prod_in : int StrMap.t -> (term * bool list) pp =
  let decl idmap ppf (x,t) = out ppf "%a : %a" var x (func idmap) t in
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
  | _ -> func idmap ppf t

let prod = prod_in StrMap.empty

let sym_rule : sym_rule pp = fun ppf r ->
  out ppf "%a ↪ %a" term (lhs r) term (rhs r)

let rule_of : sym -> rule pp = fun s ppf r -> sym_rule ppf (s,r)

let unif_rule : rule pp = rule_of Unif_rule.equiv

let rules_of : sym pp = fun ppf s -> D.list (rule_of s) ppf !(s.sym_rules)

(* for debug only *)

let typ = typ_in StrMap.empty

(*let term ppf t = out ppf "<%a printed %a>" Term.term t term t*)
(*let term = Raw.term*)

(* ends with a space if [!print_contexts = true] *)
let ctxt : ctxt pp = fun ppf ctx ->
  if !print_contexts then
    begin
      let def ppf t = out ppf " ≔ %a" term t in
      let decl ppf (x,a,t) =
        out ppf "%a%a%a" var x typ a (Option.pp def) t in
      out ppf "%a%s⊢ "
        (List.pp decl ", ") (List.rev ctx)
        (if ctx <> [] then " " else "")
    end

let typing : constr pp = fun ppf (ctx, t, u) ->
  out ppf "@[<h>%a%a : %a@]" ctxt ctx term t term u

let constr : constr pp = fun ppf (ctx, t, u) ->
  out ppf "@[<h>%a%a@ ≡ %a@]" ctxt ctx term t term u

let constrs : constr list pp = fun ppf cs ->
  let pp_sep ppf () = out ppf "@ ;" in
  out ppf "@[<v>[%a]@]" (Format.pp_print_list ~pp_sep constr) cs

let metaset : MetaSet.t pp =
  D.iter ~sep:(fun ppf () -> out ppf ",") MetaSet.iter meta

let problem : problem pp = fun ppf p ->
  out ppf
    "{ recompute=%b;@ metas={%a};@ to_solve=%a;@ unsolved=%a }"
    !p.recompute metaset !p.metas constrs !p.to_solve constrs !p.unsolved
