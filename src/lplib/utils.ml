let concat_map (f:'a -> 'b list) (l: 'a list) : 'b list =
  List.concat (List.map f l)