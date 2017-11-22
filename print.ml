(** Pretty-printing. *)

open Extra
open Terms
open Ctxt
open Sign

(* [pp oc t] pretty-prints the term [t] to the channel [oc]. *)
let pp : out_channel -> term -> unit = fun oc t ->
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
    | (Symb(s)    , _    )   -> pstring (symbol_name s)
    | (Unif(_,e)  , _    )   -> pformat "?[%a]" (Array.pp (pp `Appl) ",") e
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
  pp `Func oc (update_names t)

let pp_rule : out_channel -> def * rule -> unit = fun oc (def,rule) ->
  let pformat fmt = Printf.fprintf oc fmt in
  let (xs,lhs) = Bindlib.unmbind mkfree rule.lhs in
  let lhs = add_args (Symb(Def def)) lhs in
  let rhs = Bindlib.msubst rule.rhs (Array.map mkfree xs) in
  pformat "%a → %a" pp lhs pp rhs


(** [pp_ctxt oc ctx] pretty-prints the context [ctx] to the channel [oc]. *)
let pp_ctxt : out_channel -> Ctxt.t -> unit = fun oc ctx ->
  let pp_e oc (x,a) = Printf.fprintf oc "%s : %a" (Bindlib.name_of x) pp a in
  if ctx = [] then output_string oc "∅" else List.pp pp_e ", " oc ctx
