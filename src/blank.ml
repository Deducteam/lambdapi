let none : Earley.blank = fun buf pos ->
  (buf, pos)

let from_charset : Charset.t -> Earley.blank = fun cs ->
  let rec blank_cs buf pos =
    let (c, buf', pos') = Input.read buf pos in
    if Charset.mem cs c then blank_cs buf' pos' else (buf, pos)
  in blank_cs

let default_charset : Charset.t =
  List.fold_left Charset.add Charset.empty [' '; '\t'; '\n'; '\r']

let default : Earley.blank = from_charset default_charset

let list_of_string : string -> char list = fun s ->
  let l = ref [] in
  String.iter (fun c -> l := c :: !l) s;
  List.rev !l

let line_comments : ?blanks:Charset.t -> string -> Earley.blank =
  fun ?(blanks=default_charset) s ->
    let line_comments1 c1 =
      let blanks = Charset.add blanks c1 in
      let rec line_comments1 buf pos =
        let (c, buf', pos') = Input.read buf pos in
        if Charset.mem blanks c then line_comments1 buf' pos' else (buf, pos)
      in line_comments1
    in
    let line_comments2 c1 c2 =
      let rec line_comments2 buf pos =
        let (c, buf', pos') = Input.read buf pos in
        if Charset.mem blanks c then line_comments2 buf' pos' else
        if c = c1 && Input.get buf' pos' = c2 then
          let (buf, pos) = Input.normalize buf' (Input.line_length buf') in
          line_comments2 buf pos
        else
          (buf, pos)
      in line_comments2
    in
    let line_commentsn cc ccs =
      let rec line_commentsn state buf pos =
        let (c, buf', pos') = Input.read buf pos in
        match state with
        | None when Charset.mem blanks c ->
            line_commentsn None buf' pos'
        | None when c = cc               ->
            line_commentsn (Some((buf,pos),ccs)) buf' pos'
        | None                           ->
            (buf, pos)
        | Some(_,[])                     ->
            let (buf, pos) = Input.normalize buf' (Input.line_length buf') in
            line_commentsn None buf pos
        | Some(p,d::cs) when c = d       ->
            line_commentsn (Some(p,cs)) buf' pos'
        | Some(p,_)                      ->
            p
      in line_commentsn None
    in
    match list_of_string s with
    | []                             -> invalid_arg "empty delimiter"
    | c::_ when Charset.mem blanks c -> invalid_arg "invalid delimiter"
    | [c1]                           -> line_comments1 c1
    | [c1;c2]                        -> line_comments2 c1 c2
    | c::cs                          -> line_commentsn c cs
