(** Translation of lambdapi goals to why3 goals in propositional case *)

open Terms
open Why3

(* a type to present the list of why3 constants and lambdapi terms *)
type cnst_table = (term * Term.lsymbol) list

(** [t_goal g] output the translation of a goal [g] into a why3.*)
let rec t_goal : string -> term -> unit = fun sp g ->
    match Basics.get_args g with
    | (Symb({sym_name="P"; _}, _), [t])     ->
        let (l_prop, formula) = t_prop [] [] t in
        let symbols = List.map (fun (_, x) -> x) l_prop in
        let tsk = Why3task.declare_symbols symbols in
        let tsk = Why3task.add_goal tsk formula in
        Why3prover.test (Why3prover.prover sp) tsk
    | _                                     ->
        failwith "Goal can't be translated"

(** [t_prop l_prop ctxt p] output the translation of a lambdapi proposition
[p] with the context [ctxt] into a why3 proposition. *)
and t_prop : cnst_table -> Ctxt.t -> term -> (cnst_table * Term.term) =
    fun l_prop ctxt p ->
    let (s, args) = Basics.get_args p in
    (match s with
    | Symb({sym_name="{|and|}"; _}, _)      ->
        let (l_prop, t1) = t_prop l_prop ctxt (List.nth args 0) in
        let (l_prop, t2) = t_prop l_prop ctxt (List.nth args 1) in
        l_prop, Term.t_and t1 t2
    | Symb({sym_name="or"; _}, _)      ->
        let (l_prop, t1) = t_prop l_prop ctxt (List.nth args 0) in
        let (l_prop, t2) = t_prop l_prop ctxt (List.nth args 1) in
        l_prop, Term.t_or t1 t2
    | Symb({sym_name="imp"; _}, _)      ->
        let (l_prop, t1) = t_prop l_prop ctxt (List.nth args 0) in
        let (l_prop, t2) = t_prop l_prop ctxt (List.nth args 1) in
        l_prop, Term.t_implies t1 t2
    | Symb({sym_name="equiv"; _}, _)      ->
        let (l_prop, t1) = t_prop l_prop ctxt (List.nth args 0) in
        let (l_prop, t2) = t_prop l_prop ctxt (List.nth args 1) in
        l_prop, Term.t_iff t1 t2
    | Symb({sym_name="not"; _}, _)      ->
        let (l_prop, t) = t_prop l_prop ctxt (List.nth args 0) in
        l_prop, Term.t_not t
    | Symb(_, _)                        ->
        (* if the term [p] is in the list [l_prop] *)
        if List.exists (fun (lp_t, _) -> Basics.eq lp_t p) l_prop then
            (* then find it and return it *)
            let lp_eq = fun (lp_t, _) -> Basics.eq lp_t p in
            let (_, ct) = List.find lp_eq l_prop in
                (l_prop, Term.ps_app ct [])
            else
            (* or generate a new constant in why3 *)
                let sym = Term.create_psymbol (Ident.id_fresh "P") [] in
                let new_predicate = Term.ps_app sym [] in
                (* add the new symbol to the list and return it *)
                (p, sym)::l_prop, new_predicate
    | _                                     ->
        failwith "Proposition can't be translated ");