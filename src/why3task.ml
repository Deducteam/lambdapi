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