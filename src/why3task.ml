(** Handling tasks in why3. *)

(** [declare_symbols l] add the declaration of every symbol in [l] to [tsk] *)
let declare_symbols : Why3.Term.lsymbol list -> Why3.Task.task = fun l ->
    List.fold_left Why3.Task.add_param_decl None l

(** [add_goal tsk f] add a goal with [f] formula in the task [tsk] *)
let add_goal : Why3.Task.task -> Why3.Term.term -> Why3.Task.task =
    fun tsk f ->
    let new_goal = Why3.Ident.id_fresh "lambdapi_goal" in
    let goal = Why3.Decl.create_prsymbol new_goal in
    Why3.Task.add_prop_decl tsk Why3.Decl.Pgoal goal f

(** [add_hypothesis tsk (axiom_name, axiom_term)] add the axiom [axiom_term]
    named [axiom_name] to the Why3 task [tsk]. *)
let add_hypothesis :
    Why3.Task.task -> string * Why3.Term.term -> Why3.Task.task =
    fun tsk (axiom_name, axiom_term) ->
    let new_axiom = Why3.Ident.id_fresh axiom_name in
    let axiom = Why3.Decl.create_prsymbol new_axiom in
    Why3.Task.add_prop_decl tsk Why3.Decl.Paxiom axiom axiom_term

(** [declare_axioms l tsk] add all axioms that [l] contains to the Why3 task
    [tsk]. *)
let declare_axioms :
    (string * Why3.Term.term) list -> Why3.Task.task -> Why3.Task.task =
    fun l tsk -> List.fold_left add_hypothesis tsk l

(** [create l_prop hypothesis goal] Add all the symbols of [l_prop] in a new
 task and declare [hypothesis] as axioms and [goal] as a Why3 goal. *)
let create :
  Why3prop.cnst_table -> Why3prop.ctxt_labels -> Why3.Term.term
  -> Why3.Task.task =
  fun l_prop hypothesis goal ->
    let symbols = List.map (fun (_, x) -> x) l_prop in
    let tsk = declare_symbols symbols in
    let tsk = declare_axioms hypothesis tsk in
    add_goal tsk goal
