(** Calling provers in Why3 *)

open Timed

(** [!current_prover] contains the name of the current prover (can be changed
    by using the set prover <name> command). *)
let current_prover : string ref = ref "Alt-Ergo"

(** [time_limit] is the time limit of a prover while finding a proof. *)
let time_limit : int ref = ref 10

(** [config] read the config file of Why3 that is installed in the machine
    the default path is [~/.why3.conf]. *)
let config : Why3.Whyconf.config = Why3.Whyconf.read_config None

(** [main] get only the main section of the Why3 config *)
let main : Why3.Whyconf.main =
        let m = Why3.Whyconf.get_main config in
        Why3.Whyconf.load_plugins m; m

(** [prover provername] search and return the prover called [prover_name] *)
let prover : Pos.popt -> string -> Why3.Whyconf.config_prover =
    fun pos prover_name ->
    (* filters the set of why3 provers *)
    let fp = Why3.Whyconf.parse_filter_prover prover_name in
    let provers = Why3.Whyconf.filter_provers config fp in
    if Why3.Whyconf.Mprover.is_empty provers then
        Console.fatal pos  "[%s] not installed or not configured"
        prover_name
    else
        snd (Why3.Whyconf.Mprover.max_binding provers)

(** [env] build an empty environment *)
let env : Why3.Env.env ref = ref (Why3.Env.create_env [])

(* [init_env ()] init the environment *)
let init_env () =
    env := Why3.Env.create_env (Why3.Whyconf.loadpath main)

(** [prover_driver cp] load the config prover [cp] in the current enironment
    and return the driver of the prover. *)
let prover_driver : 
    Pos.popt -> Why3.Whyconf.config_prover -> Why3.Driver.driver =
    fun pos cp ->
    try
        Why3.Whyconf.load_driver main !env cp.Why3.Whyconf.driver []
    with e ->
        Console.fatal pos "Failed to load driver for %s: %a"
        cp.prover.prover_name
        Why3.Exn_printer.exn_printer e

(** [result prv tsk] return the result of a prover [prv] with the task
    [tsk]. *)
let result :
    Pos.popt ->
    Why3.Whyconf.config_prover ->
    Why3.Task.task ->
    Why3.Call_provers.prover_result =
    fun pos prv tsk ->
      let limit =
        {Why3.Call_provers.empty_limit with limit_time = !time_limit} in
      Why3.Call_provers.wait_on_call (Why3.Driver.prove_task
      ~limit:limit
      ~command:prv.Why3.Whyconf.command (prover_driver pos prv) tsk)

(** [answer ans] check if the answer [ans] of a prover is valid or not. *)
let answer : Why3.Call_provers.prover_answer -> bool = fun ans ->
    ans = Why3.Call_provers.Valid

(** [call sp tsk] Call the prover named [sp] with the task [tsk]. *)
let call : Pos.popt -> string -> Why3.Task.task -> Why3.Call_provers.prover_result =
    fun pos sp tsk -> result pos (prover pos sp) tsk

(* Initilizing Why3 environment. *)
let _ = init_env ()