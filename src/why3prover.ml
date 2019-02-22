(** Calling provers in Why3 *)

open Why3
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
let config : Whyconf.config = Whyconf.read_config None

(** [main] get only the main section of the Why3 config *)
let main : Whyconf.main = Whyconf.get_main config

(** [prover provername] search and return the prover called [prover_name] *)
let prover : string -> Whyconf.config_prover = fun prover_name ->
    (* filters the set of why3 provers *)
    let fp = Whyconf.parse_filter_prover prover_name in
    let provers = Whyconf.filter_provers config fp in
    if Whyconf.Mprover.is_empty provers then
        failwith (prover_name ^ " is not installed or not configured@.")
    else
        snd (Whyconf.Mprover.max_binding provers)

(** [env] build an empty environment *)
let env : Env.env ref = ref (Env.create_env [])

(* [init_env ()] init the environment *)
let init_env () =
    env := Env.create_env (Whyconf.loadpath main)

(** [prover_driver cp] load the config prover [cp] in the current enironment
    and return the driver of the prover. *)
let prover_driver : Whyconf.config_prover -> Driver.driver = fun cp ->
    try
        Whyconf.load_driver main !env cp.Whyconf.driver []
    with e ->
        Console.out 1 "Failed to load driver for alt-ergo: %a@."
    Exn_printer.exn_printer e;
    exit 1

(** [result prv tsk] return the result of a prover [prv] with the task
    [tsk]. *)
let result :
    Whyconf.config_prover -> Task.task -> Call_provers.prover_result =
    fun prv tsk ->
      let limit = {Call_provers.empty_limit with limit_time = !time_limit} in
      Call_provers.wait_on_call (Driver.prove_task
      ~limit:limit
      ~command:prv.Whyconf.command (prover_driver prv) tsk)

(** [answer ans] check if the answer [ans] of a prover is valid or not. *)
let answer : Call_provers.prover_answer -> bool = fun ans ->
    match ans with
    | Call_provers.Valid    -> true
    | _                     -> false

(** [print_result prv tsk] print the result of a prover with a task [tsk]. *)
let print_result : Whyconf.config_prover -> Task.task -> unit =
    fun prv tsk ->
    match (result prv tsk).pr_answer with
    | Call_provers.Valid ->
        Console.out 2 "Valid@."
    | _                  ->
        Console.out 1 "%s didn't found a proof@." prv.prover.prover_name

(* Initilizing Why3 environment. *)
let _ = init_env ()