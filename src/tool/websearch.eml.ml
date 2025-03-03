(*
let show_form_stream ?(message="") ?(output="") request response =
  %% response
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

    <%s! output %>

  </body>
  </html>
*)

let show_form ~from ?(message="") ?output request =
  <html>
  <style>
    .top-right-link {
        position: fixed; /* Fixe l'élément à un endroit spécifique sur la page */
        top: 10px; /* 10 pixels du haut de la page */
        right: 10px; /* 10 pixels du côté droit de la page */
        text-decoration: none; /* Enlève la décoration du texte (le soulignement) */
        background-color: #007BFF; /* Couleur de fond pour le bouton */
        color: white; /* Couleur du texte */
        padding: 10px 20px; /* Espaces autour du texte */
        border-radius: 5px; /* Bords arrondis */
        font-size: 18px; /* Taille du texte */
        text-align: center;
    }
    .top-right-link span {
      display: block;
      font-size: 12px; /* Taille de police spécifique pour ce texte */
    }
    .top-right-link:hover {
        background-color: #0056b3; /* Change la couleur de fond au survol */
    }
  </style>
  <body>
    <script>
    function incr(delta) {
      document.getElementById("from").value =
        Math.max(0,delta + Number(document.getElementById("from").value));
      document.getElementById("search").click();
    }
    </script>

    <h1><a href="https://github.com/Deducteam/lambdapi">LambdaPi</a>
     Search Engine</h1>
     
    <a href="https://github.com/Deducteam/lambdapi/issues/new" class="top-right-link"><span>Something went wrong?</span>Open an issue</a>

    <p>
    This web page offers facilities to search objects in the <a href="https://github.com/Deducteam/lambdapi">HOL-Light</a> library translated and available in 
    <a href="https://github.com/Deducteam/Dedukti/">Dedukti</a>,
    <a href="https://github.com/Deducteam/lambdapi">Lambdapi</a>  and 
    <a href="https://coq.inria.fr/">Coq/Rocq</a>.
    </p>
    <p>
    The translation has been performed using the <a href="https://github.com/Deducteam/hol2dk">hol2dk</a> tool and the resulting theorems are gathered in the Opam package coq-hol-light available in the Coq Opam repository released.
    It currently contains a translation of the Multivariate library with more than 20,000 theorems on arithmetic, wellfounded relations, lists, real numbers, integers, basic set theory, permutations, group theory, matroids, metric spaces, homology, vectors, determinants, topology, convex sets and functions, paths, polytopes, Brouwer degree, derivatives, Clifford algebra, integration, measure theory, complex numbers and analysis, transcendental numbers, real analysis, complex line integrals, etc.
    </p>
    <p>
    The <b>search</b> button answers the query. Read the <a
    href="https://lambdapi.readthedocs.io/en/latest/query_language.html">query
    language specification</a> to learn about the query language.<br>
    </p>

    <form method="POST" action="/" id="form">
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

let start ss ~port () =
  (*Common.Logger.set_debug true "e" ;*)
  Dream.run ~port
  @@ Dream.logger
  @@ Dream.memory_sessions
  @@ Dream.router [

    Dream.get  "/"
      (fun request ->
        Dream.html (show_form ~from:0 request));

    Dream.post "/"
      (fun request ->
        match%lwt Dream.form request with
        | `Ok [ "from", from; "message", message; "search", _search ] ->
          Dream.log "from1 = %s" from ;
          let from = int_of_string from in (* XXX CSC exception XXX *)
          Dream.log "from2 = %d" from ;
          let output =
            Indexing.search_cmd_html ss ~from ~how_many:100 message in
          Dream.html (show_form ~from ~message ~output request)
          (*Dream.stream (show_form_stream ~message ~output request)*)
        | _ ->
          Dream.log "no match" ;
          Dream.empty `Bad_Request);

  ]
