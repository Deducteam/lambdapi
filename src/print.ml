(** Pretty-printing. *)

open Extra
open Terms

(** [pp_symbol oc s] prints the name of the symbol [s] to the channel [oc].The
    name is qualified when the symbol is not defined in the current module. *)
let default_pp_symbol : symbol pp = fun oc s ->
  output_string oc (String.concat "." (s.sym_path @ [s.sym_name]))

let pp_symbol : symbol pp ref = ref default_pp_symbol

(** [pp_tvar oc x] prints the term variable [x] to the channel [oc]. *)
let pp_tvar : tvar pp = fun oc x ->
  output_string oc (Bindlib.name_of x)

(** [pp_meta oc m] prints the uninstantiated meta-variable [m] to [oc]. *)
let pp_meta : meta pp = fun oc m ->
  if !(m.meta_value) <> None then assert false;
  output_string oc (meta_name m)

(** [pp_term oc t] prints the term [t] to the channel [oc]. *)
let pp_term : term pp = fun oc t ->
  let out oc fmt = Printf.fprintf oc fmt in
  let rec pp (p : [`Func | `Appl | `Atom]) oc t =
    let pp_func = pp `Func in
    let pp_appl = pp `Appl in
    let pp_atom = pp `Atom in
    let pp_env oc ar =
      if Array.length ar <> 0 then out oc "[%a]" (Array.pp pp_appl ",") ar
    in
    let pp_term_env oc te =
      match te with
      | TE_Vari(m) -> out oc "?%s" (Bindlib.name_of m)
      | _          -> assert false
    in
    match (unfold t, p) with
    (* Atoms are printed inconditonally. *)
    | (Vari(x)    , _    ) -> pp_tvar oc x
    | (Type       , _    ) -> output_string oc "Type"
    | (Kind       , _    ) -> output_string oc "Kind"
    | (Symb(s)    , _    ) -> !pp_symbol oc s
    | (Meta(m,e)  , _    ) -> out oc "%a%a" pp_meta m pp_env e
    | (Patt(_,n,e), _    ) -> out oc "?%s%a" n pp_env e
    | (TEnv(t,e)  , _    ) -> out oc "<%a>%a" pp_term_env t pp_env e
    (* Applications are printed when priority is above [`Appl]. *)
    | (Appl(t,u)  , `Appl)
    | (Appl(t,u)  , `Func) -> out oc "%a %a" pp_appl t pp_atom u
    (* Abstractions and products are only printed at priority [`Func]. *)
    | (Abst(a,t)  , `Func) ->
        let (x,t) = Bindlib.unbind mkfree t in
        out oc "%a:%a => %a" pp_tvar x pp_func a pp_func t
    | (Prod(a,b)  , `Func) ->
        let (x,c) = Bindlib.unbind mkfree b in
        if Bindlib.binder_occur b then out oc "%a:" pp_tvar x;
        out oc "%a -> %a" pp_appl a pp_func c
    (* Anything else needs parentheses. *)
    | (_          , _    ) -> out oc "(%a)" pp_func t
  in
  pp `Func oc (Bindlib.unbox (lift t))

(** [pp] is a short synonym of [pp_term]. *)
let pp : term pp = pp_term

(** [pp_rule oc (s,r)] prints the rule [r] of symbol [s] to channel [oc]. *)
let pp_rule : (symbol * rule) pp = fun oc (sym,rule) ->
  let lhs = add_args (Symb(sym)) rule.lhs in
  let (_, rhs) = Bindlib.unmbind te_mkfree rule.rhs in
  Printf.fprintf oc "%a → %a" pp lhs pp rhs

(** [pp_ctxt oc ctx] prints the context [ctx] to the channel [oc]. *)
let pp_ctxt : ctxt pp = fun oc ctx ->
  let pp_e oc (x,a) = Printf.fprintf oc "%a : %a" pp_tvar x pp a in
  if ctx = [] then output_string oc "∅"
  else List.pp pp_e ", " oc (List.rev ctx)

let pp_unif : unif pp = fun oc (_,t,u) ->
  Printf.fprintf oc "%a = %a" pp t pp u

let pp_unifs : unif list pp = fun oc l ->
  match l with
  | [] -> ()
  | _ -> Printf.fprintf oc " if %a" (List.pp pp_unif ", ") l

let pp_hyp oc (s,(_,t)) = Printf.fprintf oc "%s : %a" s pp (Bindlib.unbox t)

let pp_hyps oc l = List.pp pp_hyp "\n" oc l

let sep = "------------------------------------------------------------------\n"

let pp_goal oc g = Printf.fprintf oc "%a%s%a\n" pp_hyps g.g_hyps sep pp g.g_type
