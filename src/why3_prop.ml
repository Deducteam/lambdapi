open Terms

(* a type to present the list of why3 constants and lambdapi terms *)
type cnst_table = (term * string) list

(* count the number of constants (usefull to generate new fresh constants) *)
let count_predicate = ref 0

(* generate a new why3 constants *)
let fresh_predicate () : string = 
    count_predicate := !count_predicate + 1;
    "y3p_" ^ (string_of_int !count_predicate)

(** [t_goal g] output the translation of a lamdapi goal [g] into a why3 goal. *)
let rec t_goal : term -> unit = fun g -> 
    match Basics.get_args g with
    | (Symb({sym_name="P"; _}, _), [t])     -> let _ = t_prop [] [] t in 
                                                ()
    | _                                     -> failwith "Goal can't be translated"
    
(** [t_prop l_prop ctxt p] output the translation of a lambdapi proposition [p] with the context [ctxt] into a why3 proposition. *)
and t_prop : cnst_table -> Ctxt.t -> term -> cnst_table = 
    fun l_prop ctxt p ->
    let (s, args) = Basics.get_args p in
    (match s with
    | Symb({sym_name="{|and|}"; _}, _)      -> 
        let l_prop = t_prop l_prop ctxt (List.nth args 0) in
        Console.out 1 " /\\ ";
        t_prop l_prop ctxt (List.nth args 1)
    | Symb({sym_name="or"; _}, _)      -> 
        let l_prop = t_prop l_prop ctxt (List.nth args 0) in
        Console.out 1 " \\/ ";
        t_prop l_prop ctxt (List.nth args 1)
    | Symb({sym_name="imp"; _}, _)      -> 
        let l_prop = t_prop l_prop ctxt (List.nth args 0) in
        Console.out 1 " -> ";
        t_prop l_prop ctxt (List.nth args 1)
    | Symb({sym_name="equiv"; _}, _)      -> 
        let l_prop = t_prop l_prop ctxt (List.nth args 0) in
        Console.out 1 " <-> ";
        t_prop l_prop ctxt (List.nth args 1)
    | Symb({sym_name="not"; _}, _)      -> 
        Console.out 1 " not ";
        t_prop l_prop ctxt (List.nth args 0)
    | Symb(_, _)                        ->
        (* if the term [p] is in the list [l_prop] *)
        if List.exists (fun (lp_t, _) -> Basics.eq lp_t p) l_prop then
            (* then find it and return it *)
            let (_, ct) = List.find (fun (lp_t, _) -> Basics.eq lp_t p) l_prop in
                Console.out 1 "%s" ct;
                l_prop
            else
            (* or generate a new constant in why3 *)
                let var_name = fresh_predicate () in
                Console.out 1 "%s" var_name;
                (p, var_name)::l_prop
    | _                                     -> failwith "Proposition can't be translated ");