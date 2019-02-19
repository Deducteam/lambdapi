
open Why3

let symbol_of : string -> Term.lsymbol = fun s ->
    Term.create_psymbol (Ident.id_fresh s) []

let to_symbols : string list -> Term.lsymbol list = fun l ->
    List.map (fun x -> symbol_of x) l

let atom_of : string -> Term.term = fun s ->
    Term.ps_app (symbol_of s) []

let to_atoms : string list -> Term.term list = fun l ->
    List.map (fun x -> atom_of x) l

let declare_symbols : Term.lsymbol list -> Task.task = fun l ->
    List.fold_left (fun a b -> Task.add_param_decl a b) None l


let add_goal : Task.task -> Term.term -> Task.task = fun tsk f -> 
    let goal = Decl.create_prsymbol (Ident.id_fresh "lambdapi_goal") in
    Task.add_prop_decl tsk Decl.Pgoal goal f