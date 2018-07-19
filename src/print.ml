(** Pretty-printing. *)

open Extra
open Terms

(** [pp_symbol_ref] is used to avoid module circularity (with [Sign]). *)
let pp_symbol_ref = Pervasives.ref (fun _ _ -> assert false)

(** [pp_symbol oc s] prints the name of the symbol [s] to the channel [oc].The
    name is qualified when the symbol is not defined in the current module. *)
let pp_symbol : sym pp = fun oc s ->
  Pervasives.(!pp_symbol_ref oc s)

(** [pp_tvar oc x] prints the term variable [x] to the channel [oc]. *)
let pp_tvar : tvar pp = fun oc x ->
  Format.pp_print_string oc (Bindlib.name_of x)

(** [pp_meta oc m] prints the uninstantiated meta-variable [m] to [oc]. *)
let pp_meta : meta pp = fun oc m ->
  Format.pp_print_string oc (meta_name m)

(** [pp_term oc t] prints the term [t] to the channel [oc]. *)
let pp_term : term pp = fun oc t ->
  let out oc fmt = Format.fprintf oc fmt in
  (* NOTE we apply the conventions used in [Parser.expr] for priorities. *)
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
    | (Type       , _    ) -> out oc "Type"
    | (Kind       , _    ) -> out oc "Kind"
    | (Symb(s)    , _    ) -> pp_symbol oc s
    | (Meta(m,e)  , _    ) -> out oc "%a%a" pp_meta m pp_env e
    | (Patt(_,n,e), _    ) -> out oc "?%s%a" n pp_env e
    | (TEnv(t,e)  , _    ) -> out oc "<%a>%a" pp_term_env t pp_env e
    (* Applications are printed when priority is above [`Appl]. *)
    | (Appl(t,u)  , `Appl)
    | (Appl(t,u)  , `Func) -> out oc "%a %a" pp_appl t pp_atom u
    (* Abstractions and products are only printed at priority [`Func]. *)
    | (Abst(a,t)  , `Func) ->
        let (x,t) = Bindlib.unbind t in
        out oc "%a:%a => %a" pp_tvar x pp_func a pp_func t
    | (Prod(a,b)  , `Func) ->
        let (x,c) = Bindlib.unbind b in
        if Bindlib.binder_occur b then
          out oc "!%a:%a, %a" pp_tvar x pp_appl a pp_func c
        else out oc "%a -> %a" pp_appl a pp_func c
    (* Anything else needs parentheses. *)
    | (_          , _    ) -> out oc "(%a)" pp_func t
  in
  pp `Func oc (cleanup t)

(** [pp] is a short synonym of [pp_term]. *)
let pp : term pp = pp_term

(** [pp_rule oc (s,r)] prints the rule [r] of symbol [s] to channel [oc]. *)
let pp_rule : (sym * rule) pp = fun oc (sym,rule) ->
  let lhs = add_args (Symb(sym)) rule.lhs in
  let (_, rhs) = Bindlib.unmbind rule.rhs in
  Format.fprintf oc "%a → %a" pp lhs pp rhs

(** [pp_theorem oc thm] prints the theorem [thm] to channel [oc]. *)
let pp_theorem : Proofs.theorem pp = fun oc thm ->
  let open Proofs in
  Format.fprintf oc "== Current theorem ======================\n";
  begin
    match thm.t_goals with
    | []    -> Format.fprintf oc " No more goals...\n"
    | g::gs ->
        let print_hyp (s,(_,t)) =
          Format.fprintf oc "  %s : %a\n" s pp (Bindlib.unbox t)
        in
        List.iter print_hyp g.g_hyps;
        Format.fprintf oc " ----------------------------------------\n";
        Format.fprintf oc "  %a\n" pp g.g_type;
        if gs <> [] then
          begin
            Format.fprintf oc "\n";
            Format.fprintf oc " >0< %a : %a\n" pp_meta g.g_meta pp g.g_type;
            let print_goal i g =
              Format.fprintf oc " (%i) %a : %a\n" (i+1)
                pp_meta g.g_meta pp g.g_type
            in
            List.iteri print_goal gs
          end
  end;
  Format.fprintf oc "==========================================\n"
