(** Handling tasks in why3. *)

(** [declare_symbols l] add the declaration of every symbol in [l] to [tsk] *)
let declare_symbols : Why3.Term.lsymbol list -> Why3.Task.task = fun l ->
    List.fold_left (fun a b -> Why3.Task.add_param_decl a b) None l

(** [add_goal tsk f] add a goal with [f] formula in the task [tsk] *)
let add_goal : Why3.Task.task -> Why3.Term.term -> Why3.Task.task =
    fun tsk f ->
    let new_goal = Why3.Ident.id_fresh "lambdapi_goal" in
    let goal = Why3.Decl.create_prsymbol new_goal in
    Why3.Task.add_prop_decl tsk Why3.Decl.Pgoal goal f

let add_hypothesis :
    Why3.Task.task -> string * Why3.Term.term -> Why3.Task.task =
    fun tsk (axiom_name, axiom_term) ->
    let new_axiom = Why3.Ident.id_fresh axiom_name in
    let axiom = Why3.Decl.create_prsymbol new_axiom in
    Why3.Task.add_prop_decl tsk Why3.Decl.Paxiom axiom axiom_term

let declare_axioms :
    (string * Why3.Term.term) list -> Why3.Task.task -> Why3.Task.task =
    fun l tsk ->
    List.fold_left (fun tsk' (x, term) -> add_hypothesis tsk' (x, term)) tsk l