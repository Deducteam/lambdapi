let show_form ?output request =
  <html>
  <body>

    <h1><a href="https://github.com/Deducteam/lambdapi">LambdaPi</a>
     Search Engine</h1>

    <form method="POST" action="/">
      <%s! Dream.csrf_tag request %>
      <input name="message" autofocus>
      <input type="submit" value="locate" name="locate">
      <input type="submit" value="search" name="search">
      <input type="submit" value="query" name="query">
    </form>

%   begin match output with
%   | None -> ()
%   | Some output ->
    <%s! output %>
%   end;

  </body>
  </html>

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
          let output = Indexing.locate_cmd_html message in
          Dream.html (show_form ~output request)
        | `Ok [ "message", message; "search", _search ] ->
          let output = Indexing.search_cmd_html message in
          Dream.html (show_form ~output request)
        | `Ok [ "message", message; "query", _search ] ->
          let output = Indexing.search_query_cmd_html message in
          Dream.html (show_form ~output request)
        (* debugging code
        | `Ok l ->
            let output =
              String.concat " " (List.map (fun (x,y) -> x ^ ":" ^ y) l) in
            Dream.html (show_form ~output request) *)
        | _ ->
          Dream.empty `Bad_Request);

  ]
