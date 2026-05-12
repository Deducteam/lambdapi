(** [color] tells whether colors can be used in the output. *)
let color : bool Stdlib.ref = Stdlib.ref true

(** Format transformers (colors). *)
type color = Red | Gre | Yel | Blu | Mag | Cya

type Format.stag += Color of color

let color_code = function
  | Red -> "31"
  | Gre -> "32"
  | Yel -> "33"
  | Blu -> "34"
  | Mag -> "35"
  | Cya -> "36"

let string_of_color = function
  | Red -> "red"
  | Gre -> "gre"
  | Yel -> "yel"
  | Blu -> "blu"
  | Mag -> "mag"
  | Cya -> "cya"

let color_of_string = function
  | "red" -> Red
  | "gre" -> Gre
  | "yel" -> Yel
  | "blu" -> Blu
  | "mag" -> Mag
  | "cya" -> Cya
  | s -> invalid_arg @@ "color_of_string: unknown color: [" ^ s ^ "]"

let rec mark_open_stag old = function
  | Color c -> "\027[" ^ color_code c ^ "m"
  | Format.String_tag s -> begin
    try mark_open_stag old (Color (color_of_string s))
    with Stdlib.Invalid_argument _ -> old @@ Format.String_tag s
  end
  | stag -> old stag

let rec mark_close_stag old = function
  | Color _ -> "\027[0m"
  | Format.String_tag s -> begin
    try mark_close_stag old (Color (color_of_string s))
    with Stdlib.Invalid_argument _ -> old @@ Format.String_tag s
  end
  | stag -> old stag

let update_with_color fmt =
  if Stdlib.(!color) <> Format.pp_get_mark_tags fmt () then begin
    Format.pp_set_tags fmt Stdlib.(!color);
    let old_stag_functions = Format.pp_get_formatter_stag_functions fmt () in
    let mark_open_stag = mark_open_stag old_stag_functions.mark_open_stag
    and mark_close_stag = mark_close_stag old_stag_functions.mark_close_stag
    in
    Format.pp_set_formatter_stag_functions fmt
      { old_stag_functions with mark_open_stag; mark_close_stag }
  end

let colorize k format =
  Scanf.format_from_string
    ("@{<" ^ string_of_color k ^ ">" ^ string_of_format format ^ "@}")
  format

let pp p_col printer fmt =
  update_with_color fmt;
  let a : _ format = "%a" in
  Format.fprintf fmt (p_col a) printer

let red fmt = colorize Red fmt
let gre fmt = colorize Gre fmt
let yel fmt = colorize Yel fmt
let blu fmt = colorize Blu fmt
let mag fmt = colorize Mag fmt
let cya fmt = colorize Cya fmt

(** [g_or_r cond fmt] colors the format [fmt] in green if [cond] is [true] and
    in red otherwise. *)
let g_or_r cond = if cond then gre else red
