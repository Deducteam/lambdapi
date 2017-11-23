(** Pretty-printing. *)

open Extra
open Terms
open Ctxt
open Sign

(** [pp_symbol oc s] prints the name of the symbol [s] to the channel [oc].The
    name is qualified when the symbol is not defined in the current module. *)
let pp_symbol : out_channel -> symbol -> unit = fun oc s ->
  let (path, name) =
    match s with
    | Sym(sym) -> (sym.sym_path, sym.sym_name)
    | Def(def) -> (def.def_path, def.def_name)
  in
  let full =
    if path = Stack.top Sign.loading then name
    else String.concat "." (path @ [name])
  in
  output_string oc full

(** [pp_term oc t] prints the term [t] to the channel [oc]. *)
let pp_term : out_channel -> term -> unit = fun oc t ->
  let pstring = output_string oc in
  let pformat fmt = Printf.fprintf oc fmt in
  let name = Bindlib.name_of in
  let rec pp (p : [`Func | `Appl | `Atom]) oc t =
    let t = unfold t in
    match (t, p) with
    (* Atoms are printed inconditonally. *)
    | (Vari(x)    , _    )   -> pstring (name x)
    | (Type       , _    )   -> pstring "Type"
    | (Kind       , _    )   -> pstring "Kind"
    | (Symb(s)    , _    )   -> pp_symbol oc s
    | (Unif(_,_,e), _    )   -> pformat "?[%a]" (Array.pp (pp `Appl) ",") e
    | (PVar(_)    , _    )   -> pstring "?"
    (* Applications are printed when priority is above [`Appl]. *)
    | (Appl(_,t,u), `Appl)
    | (Appl(_,t,u), `Func) -> pformat "%a %a" (pp `Appl) t (pp `Atom) u
    (* Abstractions and products are only printed at priority [`Func]. *)
    | (Abst(_,a,t), `Func)   ->
        let (x,t) = Bindlib.unbind mkfree t in
        pformat "%s:%a => %a" (name x) (pp `Func) a (pp `Func) t
    | (Prod(_,a,b), `Func)   ->
        let (x,c) = Bindlib.unbind mkfree b in
        let x = if Bindlib.binder_occur b then (name x) ^ ":" else "" in
        pformat "%s%a -> %a" x (pp `Appl) a (pp `Func) c
    (* Anything else needs parentheses. *)
    | (_          , _    )   -> pformat "(%a)" (pp `Func) t
  in
  pp `Func oc (Bindlib.unbox (lift t))

(** [pp] is a short synonym of [pp_term]. *)
let pp : out_channel -> term -> unit = pp_term

(** [pp_rule oc (s,r)] prints the rule [r] of symbol [s] to channel [oc]. *)
let pp_rule : out_channel -> def * rule -> unit = fun oc (def,rule) ->
  let (xs,lhs) = Bindlib.unmbind mkfree rule.lhs in
  let lhs = add_args (Symb(Def def)) lhs in
  let rhs = Bindlib.msubst rule.rhs (Array.map mkfree xs) in
  Printf.fprintf oc "%a → %a" pp lhs pp rhs

(** [pp_ctxt oc ctx] prints the context [ctx] to the channel [oc]. *)
let pp_ctxt : out_channel -> Ctxt.t -> unit = fun oc ctx ->
  let pp_e oc (x,a) = Printf.fprintf oc "%s : %a" (Bindlib.name_of x) pp a in
  if ctx = [] then output_string oc "∅" else List.pp pp_e ", " oc ctx
