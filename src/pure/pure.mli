(** Interface to LSP. *)

open Lplib
open Core
open Common
open Handle

val version : string

module Args : sig
  (* val debug : Bool.t Cmdliner.Term.t *)
end

module Loc_t : sig
  type source =
    | InFile of
        { dirpath : string option
        ; file : string
        }
    | ToplevelInput

  type t (* = Pos.pos *) =
  { fname : source  (** Filename or toplevel input. *)
  ; line_nb : int  (** Start line number. *)
  ; bol_pos : int  (** Position of the beginning of start line. *)
  ; line_nb_last : int  (** End line number. *)
  ; bol_pos_last : int  (** Position of the beginning of end line. *)
  ; bp : int  (** Start position. *)
  ; ep : int  (** End position. *)
  }

  val initial : source -> t
  (* val to_range : Pos. *)
end

module Pp_t : sig
  type t = string
  val to_string : t -> string
  val pp_with : Format.formatter -> t -> unit
  val str : string -> t
  val int : int -> t
  val (++) : t -> t -> t
end

module Utils : sig
  val to_range : lines:string array -> Loc_t.t -> Lang.Range.t
end

module Message : sig
  module Payload : sig
    type 'l t = { range : 'l option
                ; quickFix: 'l Lang.Qf.t list option
                ; msg: Pp_t.t
                }

    val make : ?range:'l -> ?quickFix:'l Lang.Qf.t list -> Pp_t.t -> 'l t
  end

  type 'l t = Lang.Diagnostic.Severity.t * 'l Payload.t
  val map : f:('l -> 'm) -> 'l t -> 'm t
end

module Limits : sig

  module Token : sig
    type t
    val create : unit -> t
    val set : t -> unit
  end

end

module Protect : sig

  (** This module reifies side effects into an algebraic structure.

      This is obviously very convenient for upper layer programming.

      As of today this includes feedback and exceptions. *)
  module Error : sig
    type 'l t = private
      | User of 'l Message.Payload.t
      | Anomaly of 'l Message.Payload.t
  end

  (** This "monad" could be related to "Runners in action" (Ahman, Bauer), thanks
      to Guillaume Munch-Maccagnoni for the reference and for many useful tips! *)
  module R : sig
    type ('a, 'l) t = private
      | Completed of ('a, 'l Error.t) result
      | Interrupted (* signal sent, eval didn't complete *)

    val error : ?range:'l -> string -> ('a, 'l) t
    val map : f:('a -> 'b) -> ('a, 'l) t -> ('b, 'l) t

    val map_error :
      f:('l Message.Payload.t -> 'm Message.Payload.t) -> ('a, 'l) t -> ('a, 'm) t

    (** Update the loc stored in the result, this is used by our cache-aware
        location *)
    val map_loc : f:('l -> 'm) -> ('a, 'l) t -> ('a, 'm) t
  end

  module E : sig
    type ('a, 'l) t = private
      { r : ('a, 'l) R.t
      ; feedback : 'l Message.t list
      }

    val map : f:('a -> 'b) -> ('a, 'l) t -> ('b, 'l) t
    val map_loc : f:('l -> 'm) -> ('a, 'l) t -> ('a, 'm) t
    val bind : f:('a -> ('b, 'l) t) -> ('a, 'l) t -> ('b, 'l) t
    val ok : 'a -> ('a, 'l) t
    val error : ?range:'l -> string -> ('a, 'l) t

    module O : sig
      val ( let+ ) : ('a, 'l) t -> ('a -> 'b) -> ('b, 'l) t
      val ( let* ) : ('a, 'l) t -> ('a -> ('b, 'l) t) -> ('b, 'l) t
    end
  end

  (** Must be hooked to allow [Protect] to capture the feedback. *)
  val fb_queue : Loc_t.t Message.t list ref

  (** Eval a function and reify the exceptions. Note [f] _must_ be pure, as in
      case of anomaly [f] may be re-executed with debug options. Beware, not
      thread-safe! [token] Does allow to interrupt the evaluation. *)
  val eval : token:Limits.Token.t -> f:('i -> 'o) -> 'i -> ('o, Loc_t.t) E.t

end

(** Abstract representation of a command (top-level item). *)
module Command : sig
  type t
  val equal : t -> t -> bool
  val get_pos : t -> Pos.popt
  val print : t Base.pp [@@ocaml.toplevel_printer]
end

val rangemap : Command.t list -> Term.qident RangeMap.t

(** Abstract representation of a tactic (proof item). *)
module Tactic : sig
  type t
  val equal : t -> t -> bool
  val get_pos : t -> Pos.popt
  val print : t Base.pp [@@ocaml.toplevel_printer]
end

(** Abstract representation of a proof. *)
module ProofTree : sig
  type t
  val equal : t -> t -> bool
  val fold : ('a -> Tactic.t -> int -> 'a) -> 'a -> t -> 'a
end

(** Representation of the state when at the toplevel. *)
type state

(** Representation of the state when in a proof. *)
type proof_state

module State : sig
  type t = state
  val compare : t -> t -> int
  val hash : t -> int

  module Proof : sig
    type t = proof_state
  end
  val lemmas : t -> Proof.t
  val in_state : token:Limits.Token.t -> st:t -> f:('a -> 'b) -> 'a -> ('b, Loc_t.t) Protect.E.t

end

(** [current_goals s] returns the list of open goals for proof state [s]. *)
val current_goals : State.Proof.t -> Goal.info list

module Ast : sig
  type t = Command.t
  val compare : t -> t -> int
  val hash : t -> int
  val loc : t -> Loc_t.t option
  val print : t -> Pp_t.t
  val make_info : st:State.t -> lines:string array -> t -> Lang.Ast.Info.t list option
end

module Init : sig
  val init : unit -> State.t
end

(* configuration for a document *)
module Workspace : sig
  type t = unit

  module CmdLine : sig
    type t
    val make : unit -> t
  end

  val guess :
     token:Limits.Token.t
  -> debug:bool
  -> cmdline:CmdLine.t
  -> dir:string
  -> (t, string) Result.t

  val default : debug:bool -> cmdline:CmdLine.t -> t

  val describe_guess : (t, string) Result.t -> string * string

end

module Files : sig
  type t = unit
  val make : unit -> t
end

module Parsing : sig

  module Lexer : sig
    val after : Loc_t.t -> Loc_t.t
  end

  module Parsable : sig
    type t

    val make : ?loc:Loc_t.t -> string -> t
    val loc : t -> Loc_t.t
  end

  val parse :
    token:Limits.Token.t
    -> st:State.t
    -> Parsable.t
    -> (Ast.t option, Loc_t.t) Protect.E.t

  val discard_to_dot : Parsable.t -> unit

end

(** [parse_text ~fname contents] runs the parser on the string [contents] as
    if it were a file named [fname]. It returns the list of commands it could
    parse and, either [None] if it could parse all commands, or some position
    and error message otherwise. *)
    val parse_text :
    fname:string -> string -> Command.t list * (Pos.pos * string) option

(** A goal is given by a list of assumptions and a conclusion. Each assumption
   has a name and a type. *)
type conclusion =
  | Typ of string * string (** Metavariable name and type. *)
  | Unif of string * string (** LHS and RHS of the unification goal. *)
type goal = (string * string) list * conclusion

module Goals : sig
  type ('a, 'pp) t = goal list
  (* type ('a, 'pp) reified = goal list *)

  val goals : State.t -> ('a, 'pp) t option

end

(** Result type of the [handle_command] function. *)
type command_result =
  | Cmd_OK    of state * string option
  (** Command is done. *)
  | Cmd_Proof of proof_state * ProofTree.t * Pos.popt * Pos.popt
  (** Enter proof mode (positions are for statement and qed). *)
  | Cmd_Error of Pos.popt option * string
  (** Error report. *)

(** Result type of the [handle_tactic] function. *)
type tactic_result =
  | Tac_OK    of proof_state * string option
  | Tac_Error of Pos.popt option * string

(** [initial_state fname] gives an initial state for working with the (source)
    file [fname]. The resulting state can be used by [handle_command]. *)
val initial_state : string -> state

(** [handle_command st cmd] evaluates the command [cmd] in state [st],  giving
    one of three possible results: the command is fully handled (corresponding
    to the [Cmd_OK] constructor,  the command starts a proof (corresponding to
    the [Cmd_Proof] constructor), or the command fails (corresponding  to  the
    [Cmd_Error] constuctor). *)
val handle_command : state -> Command.t -> command_result

module Interp : sig
  val interp : token:Limits.Token.t -> st:State.t -> Ast.t -> (State.t, Loc_t.t) Protect.E.t
end

(** [handle_tactic ps tac n] evaluates the tactic [tac] with [n] subproofs in
   proof state [ps], returning a new proof state (with [Tac_OK]) or an error
   (with [Tac_Error]). *)
val handle_tactic : proof_state -> Tactic.t -> int -> tactic_result

(** [end_proof st] finalises the proof which state is [st], returning a result
    at the command level for the whole theorem. This function should be called
    when all the tactics have been handled with [handle_tactic]. Note that the
    value returned by this function cannot be {!constructor:Cmd_Proof}. *)
val end_proof : proof_state -> command_result

(** [get_symbols st] returns all the symbols defined in the signature at state
    [st]. This can be used for displaying the type of symbols. *)
val get_symbols : state -> Term.sym Extra.StrMap.t

(** [set_initial_time ()] records the current imperative state as the rollback
    "time" for the [initial_state] function. This is only useful to initialise
    or reinitialise the pure interface. *)
val set_initial_time : unit -> unit
