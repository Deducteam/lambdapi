(** This modules defines a functor whose image is a parser for terms with
    applications, binary and unary operators. These terms are specified in the
    argument of the functor.

    The algorithm implemented is an extension of the Pratt parser. The
    Shunting Yard algorithm could also be used.
    @see <https://matklad.github.io/2020/04/13/simple-but-powerful-\
pratt-parsing.html>
    @see <https://dev.to/jrop/pratt-parsing> *)

(** Associativity of an operator. *)
type associativity =
  | Left
      (** If [+] is a left associative operator, [x + y + z] is parsed [(x +
          y) + z]. *)
  | Right
      (** If [+] is a right associative operator, [x + y + z] is parsed [x +
          (y + z)]. *)
  | Neither
      (** If [+] is not associative, then [(x + y) + z] is not [x + (y + z)]
          and [x + y + z] results in a syntax error. *)

type priority = float
(** Priority of operators. If [*] has a higher priority than [+], than [x + y
    * z] is parsed [x + (y * z)]. *)

(** A type to designate operators and their properties. *)
type operator =
  | Bin of associativity  (** Binary operator with an associativity. *)
  | Una  (** Unary operator. *)

(** Types and utilities on terms that are to be Pratt parsed. *)
module type SUPPORT = sig
  type term
  (** The main type of terms, that contains symbols, applications, binary and
      unary operators. *)

  type table
  (** The table is used to store available operators. *)

  val get : table -> term -> (operator * priority) option
  (** [get tbl t] returns [None] if [t] is not an operator according to table
      [tbl], and it returns the properties of the operator otherwise. *)

  val make_appl : term -> term -> term
  (** [make_appl t u] returns the application of [t] to [u], sometimes noted
      [@(t, u)], or just [t u]. *)
end

module Make : functor (Sup : SUPPORT) -> sig
  exception OpConflict of Sup.term * Sup.term
  (** Raised when there is a priority or associativiy conflict between two
      operators. The arguments are the terms that generate the conflict. *)

  exception TooFewArguments
  (** Raised when more arguments are expected. It is raised for instance on
      partial application of operators, such as [x +]. *)

  val expression : Sup.table -> Sup.term Stream.t -> Sup.term
  (** [expression tbl s] parses stream of tokens [s] with table of operators
      [tbl]. It transforms a sequence of applications to a structured
      application tree containing infix and prefix operators. For instance,
      assuming that [+] is declared infix, it transforms [3 + 5 + 2],
      represented as [@(@(@(@(3,+),5),+),2)] (where [@] is the application)
      into [(@(+(@(+,3,5)),2)].

      @raises TooFewArguments when the stream [s] is empty or does not have
                              enough elements.
      @raises OpConflict when the input terms cannot be parenthesised
                         unambiguously. *)
end =
functor
  (Sup : SUPPORT)
  ->
  struct
    type table = Sup.table

    exception OpConflict of Sup.term * Sup.term
    exception TooFewArguments

    (* NOTE: among the four functions operating on streams, only [expression]
       consumes elements from it. *)

    (** [nud tbl strm t] is the production of term [t] with {b no} left
        context.  If [t] is not an operator, [nud] is the identity. Otherwise,
        the output is a production rule. *)
    let rec nud : table -> Sup.term Stream.t -> Sup.term -> Sup.term =
     fun tbl strm t ->
      match Sup.get tbl t with
      | Some (Una, rbp) ->
          Sup.make_appl t (expression ~tbl ~rbp ~rassoc:Neither strm)
      | _ -> t

    (** [led ~tbl ~strm ~left t assoc bp] is the production of term [t] with
        left context [left]. We have the invariant that [t] is a binary
        operator with associativity [assoc] and binding power [bp]. This
        invariant is ensured while called in {!val:expression}. *)
    and led :
           tbl:table
        -> strm:Sup.term Stream.t
        -> left:Sup.term
        -> Sup.term
        -> associativity
        -> priority
        -> Sup.term =
     fun ~tbl ~strm ~left t assoc bp ->
      let rbp =
        match assoc with
        | Right -> bp *. (1. -. epsilon_float)
        | Left | Neither -> bp
      in
      Sup.(
        make_appl (make_appl t left)
          (expression ~tbl ~rbp ~rassoc:assoc strm))

    (** [expression ~tbl ~rbp ~rassoc strm] parses next token of stream
        [strm] with previous operator having a right binding power [~rbp] and
        associativity [~rassoc]. *)
    and expression :
           tbl:table
        -> rbp:priority
        -> rassoc:associativity
        -> Sup.term Stream.t
        -> Sup.term =
     fun ~tbl ~rbp ~rassoc strm ->
      (* [aux left] inspects the stream and may consume one of its elements,
         or return [left] unchanged. *)
      let rec aux (left : Sup.term) =
        match Stream.peek strm with
        | None -> left
        | Some pt -> (
            match Sup.get tbl pt with
            | Some (Bin lassoc, lbp) ->
                if lbp > rbp ||
                   (lbp = rbp && lassoc = Right && rassoc = Right)
                then
                  (* Performed before to execute side effect on stream. *)
                  let next = Stream.next strm in
                  aux (led ~tbl ~strm ~left next lassoc lbp)
                else if
                  lbp < rbp || (lbp = rbp && lassoc = Left && rassoc = Left)
                then left
                else raise (OpConflict (left, pt))
            | _ ->
                (* argument of an application *)
                let next = Stream.next strm in
                let right = nud tbl strm next in
                aux (Sup.make_appl left right) )
      in

      try
        let next = Stream.next strm in
        let left = nud tbl strm next in
        aux left
      with Stream.Failure -> raise TooFewArguments

    let expression : table -> Sup.term Stream.t -> Sup.term =
     fun tbl strm -> expression ~tbl ~rbp:0. ~rassoc:Neither strm
  end
