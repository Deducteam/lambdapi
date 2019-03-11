(** Calling provers in Why3 *)

open Timed


(* list of provers' name *)
let provers_name : (string * string) list ref =
    ref
    [
        "altergo", "Alt-Ergo";
        "eprover", "Eprover";
    ]

(** [get_name s] return the real name of a prover in Why3. *)
let get_name : string -> string = fun s ->
    try
        List.assoc s !provers_name
    with
        Not_found  -> failwith ("Failed to find `" ^ s ^ "`")

let current_prover : string ref = ref "altergo"

(** [time_limit] is the time limit of a prover while finding a proof. *)
let time_limit : int ref = ref 10

(** [config] read the config file of Why3 that is installed in the machine *)
let config : Why3.Whyconf.config = Why3.Whyconf.read_config None

(** [main] get only the main section of the Why3 config *)
let main : Why3.Whyconf.main =
        let m = Why3.Whyconf.get_main config in
        Why3.Whyconf.load_plugins m; m

(** [prover provername] search and return the prover called [prover_name] *)
let prover : string -> Why3.Whyconf.config_prover = fun prover_name ->
    (* filters the set of why3 provers *)
    let fp = Why3.Whyconf.parse_filter_prover prover_name in
    let provers = Why3.Whyconf.filter_provers config fp in
    if Why3.Whyconf.Mprover.is_empty provers then
        failwith (prover_name ^ " is not installed or not configured@.")
    else
        snd (Why3.Whyconf.Mprover.max_binding provers)

(** [env] build an empty environment *)
let env : Why3.Env.env ref = ref (Why3.Env.create_env [])

(* [init_env ()] init the environment *)
let init_env () =
    env := Why3.Env.create_env (Why3.Whyconf.loadpath main)

(** [prover_driver cp] load the config prover [cp] in the current enironment
    and return the driver of the prover. *)
let prover_driver : Why3.Whyconf.config_prover -> Why3.Driver.driver =
    fun cp ->
    try
        Why3.Whyconf.load_driver main !env cp.Why3.Whyconf.driver []
    with e ->
        Console.out 1 "Failed to load driver for alt-ergo: %a@."
    Why3.Exn_printer.exn_printer e;
    exit 1

(** [result prv tsk] return the result of a prover [prv] with the task
    [tsk]. *)
let result :
    Why3.Whyconf.config_prover ->
    Why3.Task.task ->
    Why3.Call_provers.prover_result =
    fun prv tsk ->
      let limit =
        {Why3.Call_provers.empty_limit with limit_time = !time_limit} in
      Why3.Call_provers.wait_on_call (Why3.Driver.prove_task
      ~limit:limit
      ~command:prv.Why3.Whyconf.command (prover_driver prv) tsk)

(** [answer ans] check if the answer [ans] of a prover is valid or not. *)
let answer : Why3.Call_provers.prover_answer -> bool = fun ans ->
    match ans with
    | Why3.Call_provers.Valid    -> true
    | _                     -> false

(** [print_result prv tsk] print the result of a prover with a task [tsk]. *)
let print_result : Why3.Whyconf.config_prover -> Why3.Task.task -> unit =
    fun prv tsk ->
    match (result prv tsk).pr_answer with
    | Why3.Call_provers.Valid ->
        Console.out 2 "Valid@."
    | _                  ->
        Console.out 1 "%s didn't found a proof@." prv.prover.prover_name

(** [call sp tsk] Call the prover named [sp] with the task [tsk]. *)
let call : string -> Why3.Task.task -> Why3.Call_provers.prover_result =
    fun sp tsk ->
    let prover_why3 = get_name sp in
    result (prover prover_why3) tsk

(* Initilizing Why3 environment. *)
let _ = init_env ()