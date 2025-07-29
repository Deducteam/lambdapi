
let show_form ~from ?(message="") ?output csrf_tag ~hide_description=

  <link rel="stylesheet"
  href="https://cdnjs.cloudflare.com/ajax/libs/\
  font-awesome/6.5.0/css/all.min.css">

  <button id="b_showdescription" name="showHideButton"
  onclick="toggleDescription()" style="width: 100%;">
  <i class="fas fa-angles-up"></i>
  </button>

  <script>
  function toggleDescription() {
    const descriptionSection = document.getElementById("descriptionSection");
    const hideDescrition = document.getElementById("hideDescritionSection");
    const icon = document.querySelector("button i");
  if(descriptionSection.style.display === "none"){
    descriptionSection.style.display = "block";
    hideDescrition.value = "false";
    icon.className = "fas fa-angles-up";
  } else {
    descriptionSection.style.display = "none";
    hideDescrition.value = "true";
    icon.className = "fas fa-angles-down";
  }

  }
  </script>
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
      <%s! csrf_tag %>
      <p>
      <input type="search" required="true" size="100"
        name="message" value="<%s message %>"
        onfocus="this.select();" autofocus>
      </p>
      <p>
      <input type="hidden" name="hideDescritionSection"
        id="hideDescritionSection" value="<%s hide_description %>">
      </p>
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
  let favicon_path =
    if path_in_url == "" then
      "/favicon.ico"
    else
      "/" ^ path_in_url ^ "/favicon.ico" in
  Dream.run ~port ~interface
  @@ Dream.logger
  @@ Dream.memory_sessions
  @@ Dream.router [
    Dream.head ("/" ^ path_in_url)
      (fun _ ->
        Dream.html "HTTP/1.1 301 Moved Permanently
        Date: Wed, 25 Jun 2025 13:26:55 GMT
        Server: Apache
        Location: https://www.inria.fr/
        Connection: close
        Content-Type: text/html; charset=iso-8859-1");

    Dream.get  (favicon_path)
      (fun request ->
        Dream.from_filesystem "assets" "lambdapi.ico" request);

    Dream.get  ("/" ^ path_in_url)
      (fun request ->
        let csrf_tag = Dream.csrf_tag request in
        Dream.html
          (header ^ show_form ~from:0 csrf_tag ~hide_description:"false"));

    Dream.post ("/" ^ path_in_url)
      (fun request ->
        let csrf_tag = Dream.csrf_tag request in
        match%lwt Dream.form request with
        | `Ok
          [ "from", from;
            "hideDescritionSection", hideDescritionSection;
            "message", message;
            "search", _search ] ->
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
          let header = match hideDescritionSection with
          | "true" ->
              Str.global_replace (Str.regexp_string "%%HIDE_DESCRIPTION%%")
                "none"
                header
          | _ ->
              Str.global_replace (Str.regexp_string "%%HIDE_DESCRIPTION%%")
                "block"
                header
          in
          Dream.html
            (header ^
            show_form ~from ~message ~output csrf_tag
              ~hide_description:hideDescritionSection)

        | _ ->
          Dream.log "no match" ;
          Dream.empty `Bad_Request);

  ]
