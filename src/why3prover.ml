(** Calling provers in Why3. *)

open Timed

(** [!default_prover] contains the name of the current prover (can be changed
    by using the set prover <name> command). *)
let default_prover : string ref = ref "Alt-Ergo"

(** [prover_timeout] is the time limit (in seconds) of a prover while
    finding a proof. *)
let prover_timeout : int ref = ref 10

(** [why3_config] read the config file of Why3 that is installed in the
    machine. the default path is [~/.why3.conf]. More information could be
    found in http://why3.lri.fr/api/Whyconf.html . *)
let why3_config : Why3.Whyconf.config = Why3.Whyconf.read_config None

(** [why3_main] get only the main section of the Why3 config. *)
let why3_main : Why3.Whyconf.main =
    (* Filter the configuration to get only the main information. *)
    let m = Why3.Whyconf.get_main why3_config in
    (* Load all plugins (TPTP, DIMACS, ...) and return the new config. *)
    Why3.Whyconf.load_plugins m; m

(** [prover pos provername] search and return the prover called [prover_name].
    *)
let prover : Pos.popt -> string -> Why3.Whyconf.config_prover =
    fun pos prover_name ->
    (* Filter the set of why3 provers. *)
    let fp = Why3.Whyconf.parse_filter_prover prover_name in
    (* Get the set of provers. *)
    let provers = Why3.Whyconf.filter_provers why3_config fp in
    (* Display a message if we did not find a matching prover. *)
    if Why3.Whyconf.Mprover.is_empty provers then
        Console.fatal pos  "[%s] not installed or not configured"
        prover_name
    else
    (* Return the prover configuration. *)
        snd (Why3.Whyconf.Mprover.max_binding provers)

(** [why3_env] build an empty environment. *)
let why3_env : Why3.Env.env ref = ref (Why3.Env.create_env [])

(* [init_env ()] init the environment. *)
let init_env () =
    why3_env := Why3.Env.create_env (Why3.Whyconf.loadpath why3_main)

(** [prover_driver pos cp] load the config prover [cp] in the current
    enironment and return the driver of the prover. *)
let prover_driver :
    Pos.popt -> Why3.Whyconf.config_prover -> Why3.Driver.driver =
    fun pos cp ->
    try
        Why3.Whyconf.load_driver why3_main !why3_env cp.Why3.Whyconf.driver []
    with e ->
        Console.fatal pos "Failed to load driver for %s: %a"
        cp.prover.prover_name
        Why3.Exn_printer.exn_printer e

(** [result pos prv tsk] return the result of a prover [prv] with the task
    [tsk]. *)
let result :
    Pos.popt ->
    Why3.Whyconf.config_prover ->
    Why3.Task.task ->
    Why3.Call_provers.prover_result =
    fun pos prv tsk ->
      let limit =
        {
            Why3.Call_provers.empty_limit
            with limit_time = !prover_timeout
        } in
      Why3.Call_provers.wait_on_call (Why3.Driver.prove_task
      ~limit:limit
      ~command:prv.Why3.Whyconf.command (prover_driver pos prv) tsk)

(** [answer ans] check if the answer [ans] of a prover is valid or not. *)
let answer : Why3.Call_provers.prover_answer -> bool = fun ans ->
    ans = Why3.Call_provers.Valid

(** [call pos sp tsk] call the prover named [sp] with the task [tsk]. *)
let call :
    Pos.popt -> string -> Why3.Task.task -> Why3.Call_provers.prover_result =
    fun pos sp tsk -> result pos (prover pos sp) tsk

(* Initilizing Why3 environment. *)
let _ = init_env ()