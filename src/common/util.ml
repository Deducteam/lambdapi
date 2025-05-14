let transform_ascii_to_unicode : string -> string = fun s ->
  let s = Str.global_replace (Str.regexp_string " -> ") " → " s in
  Str.global_replace (Str.regexp "\\bforall\\b") "Π" s