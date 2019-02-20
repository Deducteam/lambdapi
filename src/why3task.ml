(** Handling tasks in why3. *)

open Why3

(** [declare_symbols l] add the declaration of every symbol in [l] to [tsk] *)
let declare_symbols : Term.lsymbol list -> Task.task = fun l ->
    List.fold_left (fun a b -> Task.add_param_decl a b) None l

(** [add_goal tsk f] add a goal with [f] formula in the task [tsk] *)
let add_goal : Task.task -> Term.term -> Task.task = fun tsk f ->
    let goal = Decl.create_prsymbol (Ident.id_fresh "lambdapi_goal") in
    Task.add_prop_decl tsk Decl.Pgoal goal f