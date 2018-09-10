(** Signature of a module for keyword properties. *)
module type Spec =
  sig
    (** [id_charset] contains the characters that are not allowed to  directly
        follow a keyword (because it would make it an identifier for example).
        In general, it should correspond to characters that are can be used in
        identifiers. *)
    val id_charset : Charset.t

    (** [reserved] is a liste of words that must be rejected as identifiers as
        if they were keywords. Note that if a word is in the list, it will not
        be possible to define it as a keyword. *)
    val reserved : string list
  end

module Make(S : Spec) :
  sig
    (** [reserve s] reserves the word [s] as if it was a keyword,  although it
        will not be defined as one. The exception [Invalid_argument] is raised
        if the word [s] is already reserved. *)
    val reserve : string -> unit

    (** [mem s] tests whether [s] is a reserved word or not. *)
    val mem : string -> bool

    (** [check s] calls [Earley.give_up ()] if [s] is a reserved word.  It can
        be used to reject keywords while parsing identifiers for example. *)
    val check : string -> unit

    (** [create s] reserves the keyword [s] and returns a parser accepting the
        string [s], not followed by a character of [S.id_charset]. In the case
        where [s] is already reserved, [Invalid_argument] is raised. *)
    val create : string -> unit Earley.grammar

    (** [special s] accpets the same input as [create s], but the word [s]  is
        not reserved. *)
    val special : string -> unit Earley.grammar
  end
