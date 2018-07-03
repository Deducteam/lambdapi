(** Timed references for imperative state. This module redefines the functions
    used to update references (i.e., values of type ['a ref]), and enables the
    restoration of a saved state. *)

(** The [Time] module provides an abstract representation of time, used to set
    a point from which (monitored) updates to references are recorded to allow
    undoing/redoing the corresponding changes. *)
module Time :
  sig
    (** Point in the “timeline” of the program's execution. *)
    type t

    (** [save ()] registers the position of the program in its “timeline”. The
        returned value can then be used to “time-travel” toward this point. *)
    val save : unit -> t

    (** [restore t] has the effect of “traveling in time” towards a previously
        recorded point [t]. After calling this function, (monitored) reference
        updates made between [t] and the “time before the call” are undone. *)
    val restore : t -> unit
  end

(** [r := v] has the same effect as [Pervasives.(r := v)],  but the value that
    was stored in [r] before the update is recorded so that it may be restored
    by a subsequent call to [Time.restore]. *)
val (:=) : 'a ref -> 'a -> unit

(** [incr r] increments the integer stored in [r],  recording the old value so
    that it can be resotred by a subsequent call to [Time.restore]. *)
val incr : int ref -> unit

(** [decr r] is similar to [incr r], but it decrements the integer. *)
val decr : int ref -> unit

(** [pure_apply f v] computes the result of [f v], but reverts the (monitored)
    updates made to references in the process before returning the value. *)
val pure_apply : ('a -> 'b) -> 'a -> 'b

(** [pure_test p v] applies the predicate [p] to [v] (i.e., compute [p v]) and
    returns the result, reverting (monitored) updates made to reference if the
    result is [false]. Updates are preserved if the result is [true]. *)
val pure_test : ('a -> bool) -> 'a -> bool
