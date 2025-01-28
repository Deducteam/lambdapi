let show_form ?(message="") ?output request =
  <html>
  <body>

    <h1><a href="https://github.com/Deducteam/lambdapi">LambdaPi</a>
     Search Engine</h1>

    <p>
    The <b>search</b> button answers the query. Read the <a
    href="https://lambdapi.readthedocs.io/en/latest/query_language.html">query
    language specification</a> to learn about the query language.<br>
    </p>

    <form method="POST" action="/">
      <%s! Dream.csrf_tag request %>
      <p>
      <input type="search" required="true" size="100"
        name="message" value="<%s message %>"
        onfocus="this.select();" autofocus></p>
      <p>
      <input type="submit" value="search" name="search">
      </p>
    </form>

%   begin match output with
%   | None -> ()
%   | Some output ->
    <%s! output %>
%   end;

  </body>
  </html>

let start ~port () =
  Dream.run ~port
  @@ Dream.logger
  @@ Dream.memory_sessions
  @@ Dream.router [

    Dream.get  "/"
      (fun request ->
        Dream.html (show_form request));

    Dream.post "/"
      (fun request ->
        match%lwt Dream.form request with
        | `Ok [ "message", message; "search", _search ] ->
          let output =
            Indexing.search_cmd_html ~from:0 ~how_many:100 message in
          Dream.log "Result obtained" ;
          Dream.html (show_form ~message ~output request)
          (*Dream.stream (show_form_stream ~message ~output request)*)
        | _ ->
          Dream.empty `Bad_Request);

  ]
