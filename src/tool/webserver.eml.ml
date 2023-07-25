let show_form ?output request =
  <html>
  <body>

    <form method="POST" action="/">
      <%s! Dream.csrf_tag request %>
      <input name="message" autofocus>
      <input type="submit" value="locate" name="locate">
      <input type="submit" value="search" name="search">
    </form>

%   begin match output with
%   | None -> ()
%   | Some output ->
      <p>You entered: <b><%s output %>!</b></p>
%   end;

  </body>
  </html>

let locate_cmd s =
  try
   let qid = Parsing.Parser.Lp.parse_qid s in
   match qid with
    | [],name ->
       let items = Indexing.locate_name name in
       Format.asprintf "%a@." Indexing.pp_item_set items
   | _ ->
       Format.asprintf
        "Syntax error: an unqualified identifier was expected, found %a.%s"
         Common.Path.pp (fst qid) (snd qid)
  with
   exn ->
     Format.asprintf "%s@." (Printexc.to_string exn)

let search_cmd ?(holes_in_index=false)s =
  try
   let ptermstream = Parsing.Parser.Lp.parse_term_string "LPSearch" s in
   let pterm = Stream.next ptermstream in
   let mok _ = None in
   let items = Indexing.search_pterm ~holes_in_index ~mok [] pterm in
   Format.asprintf "%a@." Indexing.pp_item_set items
  with
   | Stream.Failure ->
      Format.asprintf "Syntax error: a term was expected"
   | exn ->
      Format.asprintf "%s@." (Printexc.to_string exn)

let start () =
  Dream.run
  @@ Dream.logger
  @@ Dream.memory_sessions
  @@ Dream.router [

    Dream.get  "/"
      (fun request ->
        Dream.html (show_form request));

    Dream.post "/"
      (fun request ->
        match%lwt Dream.form request with
        | `Ok [ "locate", _locate; "message", message ] ->
          let output = locate_cmd message in
          Dream.html (show_form ~output request)
        | `Ok [ "message", message; "search", _search ] ->
          let output = search_cmd message in
          Dream.html (show_form ~output request)
        (* debugging code
        | `Ok l ->
            let output =
              String.concat " " (List.map (fun (x,y) -> x ^ ":" ^ y) l) in
            Dream.html (show_form ~output request) *)
        | _ ->
          Dream.empty `Bad_Request);

  ]
