(** Pretty-printing for the core AST.

    The functions of this module are used for printing terms and other objects
    defined in the {!module:Terms} module.  This is mainly used for displaying
    log messages, and feedback in case of success or error while type-checking
    terms or testing convertibility. *)

open Timed
open Extra
open Terms
open Console
open Syntax

(** Logging function for printing. *)
let log_prnt = new_logger 'p' "prnt" "pretty-printing"
let log_prnt = log_prnt.logger

(** Flag controling the printing of the domains of λ-abstractions. *)
let print_domains : bool ref = Console.register_flag "print_domains" false

(** Flag controling the printing of implicit arguments. *)
let print_implicits : bool ref = Console.register_flag "print_implicits" false

(** Flag controling the printing of implicit arguments. *)
let print_meta_type : bool ref = Console.register_flag "print_meta_type" false

(** Flag controlling the printing of the context in unification. *)
let print_contexts : bool ref = Console.register_flag "print_contexts" false

(** Pretty-printing information associated to a symbol. *)
type hint =
  | No_hint
  | Prefix of unop
  | Infix of binop

let assoc : assoc pp = fun oc assoc ->
  Format.fprintf oc
    (match assoc with
     | Assoc_none -> ""
     | Assoc_left -> "left"
     | Assoc_right -> "right")

let hint : hint pp = fun oc pp_hint ->
  match pp_hint with
  | No_hint -> ()
  | Prefix(n,p,_) -> Format.fprintf oc "prefix %s %f" n p
  | Infix(n,a,p,_) -> Format.fprintf oc "infix %s %a %f" n assoc a p

(** Type for printing configurations. *)
type config = hint SymMap.t

(** Default printing configuration. *)
let empty_config = SymMap.empty

let qualified : sym pp = fun oc s ->
  Format.fprintf oc "%a.%s" Files.Path.pp s.sym_path s.sym_name

(** [config_of_sig_state ss] computes a printing configuration from [ss]. *)
let build_config : Scope.sig_state -> config = fun ss ->
  let fn_in_scope _ (sym,_) cfg =
    (*log_prnt "build_config %a" qualified sym;*)
    let sign =
      try Files.PathMap.find sym.sym_path !Sign.loaded
      with Not_found -> assert false (* Should not happen. *)
    in
    (*log_prnt "%a" Files.Path.pp sign.sign_path;
    let pr n (s,binop) =
      log_prnt "%s %a %a" n qualified s hint (Infix binop)
    in
    StrMap.iter pr !(sign.sign_binops);*)
    let h =
      let exception Hint of hint in
      try
        let fn_binop _ (s,binop) =
          (*log_prnt "%s" s.sym_name;*)
          if s == sym then raise (Hint (Infix binop)) in
        StrMap.iter fn_binop !(sign.sign_binops);
        let fn_unop _ (s,unop) =
          (*log_prnt "%s" s.sym_name;*)
          if s == sym then raise (Hint (Prefix unop)) in
        StrMap.iter fn_unop !(sign.sign_unops);
        No_hint
      with Hint h -> h
    in
    (*log_prnt (mag "%a") hint h;*)
    SymMap.add sym h cfg
  in
  let map = StrMap.fold fn_in_scope ss.in_scope SymMap.empty in
  (*let pr s h = log_prnt "%a %a" qualified s hint h in
  SymMap.iter pr map;*)
  map

(** Get the printing hint of a symbol. *)
let get_hint : config -> sym -> hint = fun cfg s ->
  try SymMap.find s cfg with Not_found -> No_hint

(** [pp_symbol oc s] prints the name of the symbol [s] to channel [oc]. *)
let pp_symbol : config -> sym pp = fun cfg oc s ->
  if SymMap.mem s cfg then Format.pp_print_string oc s.sym_name
  else Format.fprintf oc "%a.%s" Files.Path.pp s.sym_path s.sym_name
    (*FIXME: handle aliases. *)

(** [pp_tvar oc x] prints the term variable [x] to the channel [oc]. *)
let pp_tvar : tvar pp = fun oc x ->
  Format.pp_print_string oc (Bindlib.name_of x)

(** [pp_meta oc m] prints the uninstantiated meta-variable [m] to [oc]. *)
let rec pp_meta : config -> meta pp = fun cfg oc m ->
  if !print_meta_type then
    Format.fprintf oc "(%s:%a)" (meta_name m) (pp_term cfg) !(m.meta_type)
  else
    Format.pp_print_string oc (meta_name m)

(** [pp_term oc t] prints the term [t] to the channel [oc]. *)
and pp_term : config -> term pp = fun cfg oc t ->
  let out = Format.fprintf in
  (* The possible priority levels are [`Func] (top level, including
     abstraction or product), [`Appl] (application) and [`Atom] (smallest
     priority). *)
  let rec pp (p : [`Func | `Appl | `Atom]) oc t =
    let (h, args) = Basics.get_args t in
    let pp_appl h args =
      match args with
      | []   -> pp_head (p <> `Func) oc h
      | args ->
          if p = `Atom then out oc "(";
          pp_head true oc h;
          List.iter (out oc " %a" (pp `Atom)) args;
          if p = `Atom then out oc ")"
    in
    match h with
    | Symb(s) when not !print_implicits ->
        begin
          let args = Basics.expl_args s args in
          match get_hint cfg s with
          | No_hint -> pp_appl h args
          | Prefix(_) -> pp_appl h args
          | Infix(op,_,_,_) ->
              begin
                match args with
                | l::r::[] ->
                    if p <> `Func then out oc "(";
                    (* Can be improved by looking at symbol priority. *)
                    out oc "%a %s %a" (pp `Appl) l op (pp `Appl) r;
                    if p <> `Func then out oc ")"
                | l::r::ts ->
                    if p <> `Func then out oc "(";
                    out oc "(";
                    (* Can be improved by looking at symbol priority. *)
                    out oc "%a %s %a" (pp `Appl) l op (pp `Appl) r;
                    out oc ")";
                    List.iter (out oc " %a" (pp `Atom)) ts;
                    if p <> `Func then out oc ")"
                | _ -> pp_appl h args
              end
        end
    | _       -> pp_appl h args
  and pp_head wrap oc t =
    let pp_env oc ar =
      if ar <> [||] then out oc "[%a]" (Array.pp (pp `Appl) ",") ar
    in
    let pp_term_env oc te =
      match te with
      | TE_Vari(m) -> out oc "%s" (Bindlib.name_of m)
      | _          -> assert false
    in
    match unfold t with
    (* Application is handled separately, unreachable. *)
    | Appl(_,_)   -> assert false
    (* Forbidden cases. *)
    | Wild        -> assert false
    | TRef(_)     -> assert false
    (* Atoms are printed inconditonally. *)
    | Vari(x)     -> pp_tvar oc x
    | Type        -> out oc "TYPE"
    | Kind        -> out oc "KIND"
    | Symb(s)     -> pp_symbol cfg oc s
    | Meta(m,e)   -> out oc "%a%a" (pp_meta cfg) m pp_env e
    | Patt(_,n,e) -> out oc "$%s%a" n pp_env e
    | TEnv(t,e)   -> out oc "$%a%a" pp_term_env t pp_env e
    (* Product and abstraction (only them can be wrapped). *)
    | Abst(a,b)   ->
        if wrap then out oc "(";
        out oc "λ";
        let (x,t) = Bindlib.unbind b in
        if Bindlib.binder_occur b then out oc "%a" pp_tvar x else out oc "_";
        if !print_domains then out oc ": %a" (pp `Func) a;
        out oc ", %a" (pp `Func) t;
        if wrap then out oc ")"
    | Prod(a,b)   ->
        if wrap then out oc "(";
        let (x,t) = Bindlib.unbind b in
        if Bindlib.binder_occur b then
          out oc "Π%a: %a, %a" pp_tvar x (pp `Func) a (pp `Func) t
        else
          out oc "%a → %a" (pp `Appl) a (pp `Func) t;
        if wrap then out oc ")"
    | LLet(a,t,b) ->
        if wrap then out oc "(";
        let (x,u) = Bindlib.unbind b in
        if Bindlib.binder_occur b then out oc "%a" pp_tvar x else out oc "_";
        if !print_domains then out oc ": %a" (pp `Atom) a;
        out oc " ≔ %a in %a" (pp `Atom) t (pp `Atom) u;
        if wrap then out oc ")"
  in
  pp `Func oc (cleanup t)

(** [pp_rule oc (s,h,r)] prints the rule [r] of symbol [s] to the output
   channel [oc]. *)
let pp_rule : config -> (sym * rule) pp
  = fun cfg oc (s,r) ->
  let lhs = Basics.add_args (Symb s) r.lhs in
  let (_, rhs) = Bindlib.unmbind r.rhs in
  Format.fprintf oc "%a ↪ %a" (pp_term cfg) lhs (pp_term cfg) rhs

(** [pp_ctxt oc ctx] displays context [ctx] if {!val:print_contexts} is
    true, with [ ⊢ ] after; and nothing otherwise. *)
let pp_ctxt : config -> ctxt pp = fun cfg oc ctx ->
  let pp = pp_term cfg in
  let pp_ctxt : ctxt pp = fun oc ctx ->
    let pp_e oc (x,a,t) =
      match t with
      | None    -> Format.fprintf oc "%a:%a" pp_tvar x pp a
      | Some(t) -> Format.fprintf oc "%a:%a ≔ %a" pp_tvar x pp a pp t
    in
    if ctx = [] then Format.pp_print_string oc "∅"
    else List.pp pp_e ", " oc (List.rev ctx)
  in
  let out = if !print_contexts then Format.fprintf else Format.ifprintf in
  out oc "%a ⊢ " pp_ctxt ctx

(** [pp_constr oc (t,u)] prints the unification constraints [(t,u)] to the
    output channel [oc]. *)
let pp_constr : config -> constr pp
  = fun cfg oc (ctx, t, u) ->
  Format.fprintf oc "%a%a ≡ %a"
    (pp_ctxt cfg) ctx (pp_term cfg) t (pp_term cfg) u

(** [pp_constr oc p] prints the unification problem [p] to the
    output channel [oc]. *)
let pp_problem : config -> problem pp = fun cfg oc p ->
  Format.fprintf oc "{ to_solve = [%a]; unsolved = [%a]; recompute = %b }"
    (List.pp (pp_constr cfg) "; ") p.to_solve
    (List.pp (pp_constr cfg) "; ") p.unsolved
    p.recompute

(** Default printing functions (with empty configuration). *)
let symbol = pp_symbol empty_config
let meta = pp_meta empty_config
let term = pp_term empty_config
let constr = pp_constr empty_config
let rule = pp_rule empty_config
let ctxt = pp_ctxt empty_config
let problem = pp_problem empty_config
