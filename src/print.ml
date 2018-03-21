(** Pretty-printing. *)

open Extra
open Terms
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

let pp_tvar : out_channel -> tvar -> unit = fun oc x ->
  output_string oc (Bindlib.name_of x)
  (* Printf.fprintf oc "%s{%i}" (Bindlib.name_of x) (Bindlib.uid_of x) *)

let pp_meta : out_channel -> meta -> unit = fun oc m ->
  Printf.fprintf oc "?%s" (name_of_meta m)
    
(** [pp_term oc t] prints the term [t] to the channel [oc]. *)
let pp_term : out_channel -> term -> unit = fun oc t ->
  let pstring = output_string oc in
  let pformat fmt = Printf.fprintf oc fmt in
  let rec pp (p : [`Func | `Appl | `Atom]) oc t =
    let t = unfold t in
    match (t, p) with
    (* Atoms are printed inconditonally. *)
    | (Vari(x)  , _    ) -> pp_tvar oc x
    | (Type     , _    ) -> pstring "Type"
    | (Kind     , _    ) -> pstring "Kind"
    | (Symb(s)  , _    ) -> pp_symbol oc s
    | (Meta(m,e), _    ) -> pformat "?%i[%a]" m.meta_key
                                (Array.pp (pp `Appl) ",") e
    | (ITag(i)  , _    ) -> pformat "[%i]" i
    (* Applications are printed when priority is above [`Appl]. *)
    | (Appl(t,u), `Appl)
    | (Appl(t,u), `Func) -> pformat "%a %a" (pp `Appl) t (pp `Atom) u
    (* Abstractions and products are only printed at priority [`Func]. *)
    | (Abst(a,t), `Func) ->
        let (x,t) = Bindlib.unbind mkfree t in
        pformat "%a:%a => %a" pp_tvar x (pp `Func) a (pp `Func) t
    | (Prod(a,b), `Func) ->
        let (x,c) = Bindlib.unbind mkfree b in
        if Bindlib.binder_occur b then pformat "%a:" pp_tvar x;
        pformat "%a -> %a" (pp `Appl) a (pp `Func) c
    (* Anything else needs parentheses. *)
    | (_        , _    ) -> pformat "(%a)" (pp `Func) t
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
let pp_ctxt : out_channel -> ctxt -> unit = fun oc ctx ->
  let pp_e oc (x,a) = Printf.fprintf oc "%a : %a" pp_tvar x pp a in
  if ctx = [] then output_string oc "∅"
  else List.pp pp_e ", " oc (List.rev ctx)
