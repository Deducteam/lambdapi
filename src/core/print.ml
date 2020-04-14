(** Pretty-printing for the core AST.

    The functions of this module are used for printing terms and other objects
    defined in the {!module:Terms} module.  This is mainly used for displaying
    log messages, and feedback in case of success or error while type-checking
    terms or testing convertibility. *)

open Timed
open Extra
open Terms

(** Flag controling the printing of the domains of λ-abstractions. *)
let print_domains : bool ref = Console.register_flag "print_domains" false

(** Flag controling the printing of implicit arguments. *)
let print_implicits : bool ref = Console.register_flag "print_implicits" false

(** Flag controling the printing of implicit arguments. *)
let print_meta_type : bool ref = Console.register_flag "print_meta_type" false

(** Flag controlling the printing of the context in unification. *)
let print_contexts : bool ref = Console.register_flag "print_contexts" false

(** Type for printing configuration. *)
type config =
  { pc_scope : SymSet.t
  ; pc_infix : string SymMap.t }

(** Default printing configuration. *)
let empty_config =
  { pc_scope = SymSet.empty
  ; pc_infix = SymMap.empty }

(** [build_scope in_scope] builds the set of symbols in scope from a map from
   string to [sym * popt] map. *)
let build_scope : (sym * Pos.popt) StrMap.t -> SymSet.t = fun in_scope ->
  let fn _ x set =
    let (sym, _) = x in
    SymSet.add sym set
  in
  StrMap.fold fn in_scope SymSet.empty

(** [build_infix binops] builds a map from symbol to string from a map from
   string to [sym * binop]. *)
let build_infix : (sym * Syntax.binop) StrMap.t -> string SymMap.t
  = fun binops ->
  let fn name x imap =
    let (sym, _binop) = x in
    SymMap.add sym name imap
  in
  StrMap.fold fn binops SymMap.empty

(** [config_of_sig_state ss] computes a printing configuration from [ss]. *)
let config_of_sig_state : Scope.sig_state -> config = fun ss ->
  { pc_scope = build_scope ss.in_scope
  ; pc_infix = build_infix !(ss.signature.sign_binops) }

(** Tell whether a symbol is infix. *)
let infix : config -> sym -> string option = fun cfg s ->
  SymMap.find_opt s cfg.pc_infix

(** [pp_symbol oc s] prints the name of the symbol [s] to channel [oc]. *)
let pp_symbol : config -> sym pp = fun cfg oc s ->
  if SymSet.mem s cfg.pc_scope then
    Format.pp_print_string oc s.sym_name
  else
    Format.fprintf oc "%a.%s" Files.Path.pp s.sym_path s.sym_name
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
    let args =
      if !print_implicits then args else
      let impl =  match h with Symb(s) -> s.sym_impl | _ -> [] in
      let rec filter_impl impl args =
        match (impl, args) with
        | ([]         , _      ) -> args
        | (true ::impl, _::args) -> filter_impl impl args
        | (false::impl, a::args) -> a :: filter_impl impl args
        | (_          , []     ) -> args
      in
      filter_impl impl args
    in
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
    | Symb(s) ->
        begin
          match infix cfg s with
          | None -> pp_appl h args
          | Some op ->
              begin
                match Basics.expl_args s args with
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
    | Patt(_,n,e) -> out oc "&%s%a" n pp_env e
    | TEnv(t,e)   -> out oc "&%a%a" pp_term_env t pp_env e
    (* Product and abstraction (only them can be wrapped). *)
    | Abst(a,t)   ->
        if wrap then out oc "(";
        let pp_arg oc (x,a) =
          if !print_domains then out oc "(%a:%a)" pp_tvar x (pp `Func) a
          else pp_tvar oc x
        in
        let (x,t) = Bindlib.unbind t in
        out oc "λ%a" pp_arg (x,a);
        let rec pp_absts oc t =
          match unfold t with
          | Abst(a,t) -> let (x,t) = Bindlib.unbind t in
                         out oc " %a%a" pp_arg (x,a) pp_absts t
          | _         -> out oc ", %a" (pp `Func) t
        in
        pp_absts oc t;
        if wrap then out oc ")"
    | Prod(a,b)   ->
        if wrap then out oc "(";
        let pp_arg oc (x,a) = out oc "(%a:%a)" pp_tvar x (pp `Func) a in
        let (x,c) = Bindlib.unbind b in
        if Bindlib.binder_occur b then
          begin
            out oc "∀%a" pp_arg (x,a);
            let rec pp_prods oc c =
              match unfold c with
              | Prod(a,b) when Bindlib.binder_occur b ->
                  let (x,b) = Bindlib.unbind b in
                  out oc " %a%a" pp_arg (x,a) pp_prods b
              | _                                      ->
                  out oc ", %a" (pp `Func) c
            in
            pp_prods oc c
          end
        else
          out oc "%a ⇒ %a" (pp `Appl) a (pp `Func) c;
        if wrap then out oc ")"
    | LLet(a,t,u) ->
        if wrap then out oc "(";
        let x, u = Bindlib.unbind u in
        out oc "let %a" pp_tvar x;
        if !print_domains then out oc ":%a" (pp `Atom) a;
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
  Format.fprintf oc "%a → %a" (pp_term cfg) lhs (pp_term cfg) rhs

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
