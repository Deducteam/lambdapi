
let show_form ~from ?(message="") ?output request =
  <html>
  <body>

    <script>
    function incr(delta) {
      document.getElementById("from").value =
        Math.max(0,delta + Number(document.getElementById("from").value));
      document.getElementById("search").click();
    }
    </script>

    <form method="POST" id="form">
      <%s! Dream.csrf_tag request %>
      <p>
      <input type="search" required="true" size="100"
        name="message" value="<%s message %>"
        onfocus="this.select();" autofocus></p>
      <p>
      <input type="submit" value="search" id="search" name="search">
      </p>

%   begin match output with
%   | None ->
       <input type="hidden" name="from" value="<%s string_of_int from %>">
%   | Some output ->
    <p>
    <input type="number" required="true" style="width: 5em" min="0" id="from"
      name="from" value="<%s string_of_int from %>" onfocus="this.select()">
    <input type="button"
      name="prev" value="Prev" onclick="incr(-100)">
    <input type="button"
      name="next" value="Next" onclick="incr(100)">
    </p>
    <%s! output %>
%   end;
    </form>

  </body>
  </html>

let start ~header ss ~port ~dbpath ~path_in_url () =
  (*Common.Logger.set_debug true "e" ;*)
  let interface = "0.0.0.0" in
  Dream.run ~port ~interface
  @@ Dream.logger
  @@ Dream.memory_sessions
  @@ Dream.router [

    Dream.get  ("/" ^ path_in_url)
      (fun request ->
        Dream.html (header ^ show_form ~from:0 request));

    Dream.post ("/" ^ path_in_url)
      (fun request ->
        match%lwt Dream.form request with
        | `Ok [ "from", from; "message", message; "search", _search ] ->
          Dream.log "from1 = %s" from ;
          let from = int_of_string from in (* XXX CSC exception XXX *)
          Dream.log "from2 = %d" from ;
          if Timed.(!Common.Console.verbose) >= 2 then
            Dream.log "Received request = %s" message;
          let output =
            Indexing.search_cmd_html ss ~from ~how_many:100
            message ~dbpath in
          if Timed.(!Common.Console.verbose) >= 3 then
            Dream.log "sending response: %s" output;
            let output = header ^ output in
          Dream.html (show_form ~from ~message ~output request)
          (*Dream.stream (show_form_stream ~message ~output request)*)
        | _ ->
          Dream.log "no match" ;
          Dream.empty `Bad_Request);

  ]
