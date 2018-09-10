(** [none] is a blank function that does not parse anything. *)
val none : Earley.blank

(** [default] is a blank function that ignores an arbitrary number of  spacing
    characters. They include [' '], ['\t'], ['\r'] and ['\n']. *)
val default : Earley.blank

(** [from_charset cs] is a blank function that ignores an arbitrary number  of
    characters from the character set [cs]. *)
val from_charset : Charset.t -> Earley.blank

(** [line_comments ?blanks=cs delim] is a blank function that behaves the same
    as [from_charset cs], but it also ignores single-line comments starting by
    [delim]. The exception [Invalid_argument] when [delim] is empty or when it
    starts with a character of [cs]. *)
val line_comments : ?blanks:Charset.t -> string -> Earley.blank
