let default_header =
{|<style>
  .snippet {
    border: 1px solid grey;
    color: red;
    padding: 0 3px 0 3px;
    line-height: 1.6;
  }
</style>
<h1><a href="https://github.com/Deducteam/lambdapi">LambdaPi</a>
Search Engine</h1>
<div id="descriptionSection" style="display: %%HIDE_DESCRIPTION%%">
  <p>
    The <b>search</b> button answers the query. Read the <a href=
    "https://lambdapi.readthedocs.io/en/latest/query_language.html">
    query language specification</a> to learn about the query language.
    <br>The query language also uses the <a
    href="https://lambdapi.readthedocs.io/en/latest/terms.html">
    Lambdapi terms syntax</a>.<br> with the possibility to use,
    for commodity, "forall" and "->"  instead of "Π" and "→" respectively
    (results are displayed with the Unicode symbols "Π" and "→" though).
    In particular, the following constructors can come handy for
    writing queries:<br>
    </p>
    <ul>
      <li>an anonymous function<span class="snippet">λ (x:A) y z,t</span>
        mapping <span class="snippet">x</span>, <span class="snippet">y
        </span> and <span class="snippet">z</span> (of type <span
        class="snippet">A</span> for <span class="snippet">x</span>) to
        <span class="snippet">t</span>.</li>
      <li>a dependent product
        <span class="snippet">forall (x:A) y z,T</span></li>
      <li>a non-dependent product <span class="snippet">A -> T</span>
       (syntactic sugar for <span class="snippet">forall x:A,T</span> when
        <span class="snippet">x</span> does not occur in <span class=
        "snippet">T</span>)</li>
  </ul>
</div>
|}

(*--------------------------------------------------------------------------*)
(** Functions on strings *)
(*--------------------------------------------------------------------------*)

let b = "\x1b[1m" (* start bold *)
let r = "\x1b[0m" (* end bold *)

let nat_of_string s =
  match int_of_string_opt s with
  | Some k when k >= 0 -> k
  | _ -> Common.Error.fatal_no_pos "invalid integer"

let float_of_string s =
  match float_of_string_opt s with
  | Some k when k >= 0. -> k
  | _ -> Common.Error.fatal_no_pos "invalid float number"

(** [remove_prefix p s] returns the subtring of [s] starting at position
    [String.length p]. *)
let remove_prefix prefix s =
  let n = String.length prefix in
  String.sub s n (String.length s - n)

let _ = assert (remove_prefix "--debug=" "--debug=tu" = "tu")

let parse_path s =
  try Parsing.Parser.path_of_string s
  with Common.Error.Fatal(_,m) -> raise (Common.Error.Fatal(None,m))

let parse_qident s =
  try Parsing.Parser.qident_of_string s
  with Common.Error.Fatal(_,m) -> raise (Common.Error.Fatal(None,m))

(** [split_first c s] returns [Some(s1,s2)] such that [s=s1^c^s2] and [c] does
    not occur in [s1], and [None] otherwise. *)
let split_first c s =
  let n = String.length s in
  let i = ref 0 in
  while !i < n && s.[!i] != c do incr i done;
  let i = !i in
  if i = n then None
  else Some (String.sub s 0 i, String.sub s (i + 1) (n - i - 1))

let _ = assert (split_first ':' "ab:cd" = Some("ab","cd"))
let _ = assert (split_first ':' ":cd" = Some("","cd"))
let _ = assert (split_first ':' "ab:" = Some("ab",""))

let parse_map_dir s =
  match split_first ':' s with
  | Some(s,dir) -> Common.Library.add_mapping (parse_path s, dir)
  | None -> Common.Error.fatal_no_pos "wrong argument: %s" s

(*-------------------------------------------------------------------------*)
(* Type of a command line option *)
(*-------------------------------------------------------------------------*)

type handle =
  | NoArg of (unit -> unit)
  | Next of string * (string -> unit)
  | Suffix of string * (string -> unit)

type opt =
  { opt_name: string
  ; opt_short: string option
  ; opt_desc: string
  ; opt_handle: handle }

let find_option arg =
  let rec find = function
    | [] -> None
    | o :: options ->
        match o.opt_handle with
        | Suffix _ ->
            if String.starts_with ~prefix:o.opt_name arg then Some o
            else find options
        | _ ->
            let eq =
              match o.opt_short with
              | None -> arg = o.opt_name
              | Some s -> arg = s || arg = o.opt_name
            in
            if eq then Some o else find options
  in find

let parse_options options =
  let rec parse args =
    match args with
    | [] -> []
    | arg::other_args ->
        if arg="" then Common.Error.fatal_no_pos "empty argument"
        else if arg.[0] <> '-' then args
        else
          match find_option arg options with
          | None -> Common.Error.fatal_no_pos "unknown option: %s" arg
          | Some o ->
              match o.opt_handle with
              | NoArg h -> h(); parse other_args
              | Suffix(_,h) ->
                  h (remove_prefix o.opt_name arg); parse other_args
              | Next(_,h) ->
                  match other_args with
                  | [] ->
                      Common.Error.fatal_no_pos
                        "option %s has no argument" arg
                  | arg::other_args -> h arg; parse other_args
  in parse

let print_option o =
  match o.opt_short with
  | None ->
      begin
        match o.opt_handle with
        | NoArg _ ->
            Printf.printf "%s%s%s\n  %s" b o.opt_name r o.opt_desc
        | Next(arg,_) ->
            Printf.printf "%s%s %s%s\n  %s" b o.opt_name arg r o.opt_desc
        | Suffix(arg,_) ->
            Printf.printf "%s%s%s%s\n  %s" b o.opt_name arg r o.opt_desc
      end
  | Some s ->
      match o.opt_handle with
      | NoArg _ ->
          Printf.printf "%s%s, %s%s\n  %s" b s o.opt_name r o.opt_desc
      | Next(arg,_) ->
          Printf.printf "%s%s %s, %s %s%s\n  %s"
            b s arg o.opt_name arg r o.opt_desc
      | Suffix(arg,_) ->
          Printf.printf "%s%s%s, %s%s%s\n  %s"
            b s arg o.opt_name arg r o.opt_desc

(*--------------------------------------------------------------------------*)
(** General command line options *)
(*--------------------------------------------------------------------------*)

let opt_debug =
  { opt_name = "--debug="
  ; opt_short = None
  ; opt_handle = Suffix("FLAGS",Common.Logger.set_default_debug)
  ; opt_desc =
{|Enables the debugging flags specified in FLAGS. Every character of FLAGS
  correspond to a flag. The available values are:|}
^ let f (k,d) = Printf.sprintf "\n    %c: %s" k d in
  String.concat "" (List.map f (Common.Logger.log_summary())) }

let opt_verbose =
  { opt_name = "--verbose="
  ; opt_short = Some "-v"
  ; opt_handle =
      Suffix("INT",
             fun v -> Common.Console.set_default_verbose (nat_of_string v))
  ; opt_desc =
{|Set the verbosity level to INT. A value smaller or equal to 0 will disable
  all printing (on standard output). Greater numbers lead to more and more
  informations being written to standard output. In the case of the websearch
  command, a value larger or equal to 2 will print the requests received by
  the server. A value larger than will also print the responses sent by the
  server.|} }

let opt_no_colors =
  { opt_name = "--no-colors"
  ; opt_short = None
  ; opt_handle = NoArg(fun () -> Lplib.Color.color := false)
  ; opt_desc =
{|Disable the use of colors when printing to the terminal. Note that the
  default behaviour is to rely on ANSI escape sequences in order to make the
  debugging logs more readable.|} }

let opt_record_time =
  { opt_name = "--record-time"
  ; opt_short = None
  ; opt_handle = NoArg(fun () -> Common.Debug.do_record_time := true)
  ; opt_desc =
{|Print statistics on the time spent in different tasks (parsing, typing, …).
  Note that it slows down the program.|} }

let opt_no_warnings =
  { opt_name = "--no-warnings"
  ; opt_short = Some "-w"
  ; opt_handle = NoArg (fun () -> Common.Error.no_warnings := true)
  ; opt_desc = "Disable the printing of all warnings." }

let general_options =
  [ opt_debug
  ; opt_verbose
  ; opt_no_colors
  ; opt_record_time
  ; opt_no_warnings ]

(*--------------------------------------------------------------------------*)
(** Command line options for type-checking *)
(*--------------------------------------------------------------------------*)

let opt_lib_root =
  { opt_name = "--lib-root="
  ; opt_short = None
  ; opt_handle = Suffix("DIR", fun v -> Common.Library.set_lib_root (Some v))
  ; opt_desc =
{|Set the library root to be the directory DIR. The library root is a common
  path under which every module is placed. It has the same purpose as the root
  directory "/" of Unix systems. In fact it is possible to "mount" directories
  under the library root with the "--map-dir" option. Lambdapi uses DIR as
  library root if it is provided, otherwise it uses
  $LAMBDAPI_LIB_ROOT/lib/lambdapi/lib_root if the environment variable
  LAMBDAPI_LIB_ROOT is set, then $OPAM_SWITCH_PREFIX/lib/lambdapi/lib_root
  if OPAM_SWITCH_PREFIX is set or it uses /usr/local/lib/lambdapi/lib_root.|}
}

let opt_map_dir =
  { opt_name = "--map-dir="
  ; opt_short = None
  ; opt_handle = Suffix("MOD:DIR", parse_map_dir)
  ; opt_desc =
{|Map all the modules having MOD as a prefix of their module path to files
  under the directory DIR. The corresponding modules under the library root
  are then rendered inaccessible. This option is useful during the development
  of a library, before it can be installed in the expected folder under the
  library root.|} }

let opt_gen_obj =
  { opt_name = "--gen-obj"
  ; opt_short = Some "-c"
  ; opt_handle = NoArg (fun () -> Handle.Compile.gen_obj := true)
  ; opt_desc =
{|Produce object files with the ".lpo" extension. These object files can then
  be read during subsequent calls to avoid re-type-checking fo the
  corresponding source file. Note that an object file is only used when it is
  up to date (i.e., more recent than the source). If that is not the case then
 the outdated file is overwritten.|} }

let timeout = Stdlib.ref None

let opt_timeout =
  { opt_name = "--timeout="
  ; opt_short = None
  ; opt_handle = Suffix("INT", fun v -> timeout := Some(nat_of_string v))
  ; opt_desc =
{|Timeout after INT seconds. The program is interrupted with an error as soon
  as the specified number of seconds is elapsed.|} }

let opt_too_long =
  { opt_name = "--too-long"
  ; opt_short = None
  ; opt_handle = Suffix("FLOAT",
                    fun v -> Handle.Command.too_long := float_of_string v)
  ; opt_desc =
{|Print a warning every time that a command requires more than FLOAT seconds
  to execute. The command is not interrupted.|} }

let opt_no_sr_check =
  { opt_name = "--no-sr-check"
  ; opt_short = None
  ; opt_handle = NoArg(fun () -> Handle.Command.sr_check := false)
  ; opt_desc =
      "Disable the verification that rewrite rules preserve typing." }

let opt_db =
  { opt_name = "--db="
  ; opt_short = None
  ; opt_handle = Suffix("FILE", fun v -> Tool.Indexing.the_dbpath := v)
  ; opt_desc =
      "Index file to use for search queries (default is ~/.LPSearch.db)." }

let rule_files = ref []

let opt_rules =
  { opt_name = "--rules="
  ; opt_short = None
  ; opt_handle = Suffix("FILE", fun v -> rule_files := v::!rule_files)
  ; opt_desc =
{|File holding rewriting rules applied before indexing. Use this option
  multiple times to fetch rules from several files.|} }

let compile_options =
  opt_lib_root
  :: opt_map_dir
  :: opt_gen_obj
  :: opt_timeout
  :: opt_too_long
  :: opt_no_sr_check
  :: opt_db
  :: opt_rules
  :: general_options

(*--------------------------------------------------------------------------*)
(** Type for commands *)
(*--------------------------------------------------------------------------*)

type cmd =
  { name: string
  ; args: string
  ; summary: string
  ; desc: string
  ; options: opt list }

let print_usage c =
  Printf.printf
{|%sUSAGE:%s lambdapi %s %s

%s
|} b r c.name c.args c.desc;
  if c.options <> [] then
    Printf.printf
{|
%sOPTIONS:%s
|} b r;
  let cmp_opt o1 o2 = Stdlib.compare o1.opt_name o2.opt_name in
  List.iter print_option (List.sort cmp_opt c.options)

let add_help c =
  let handle = ref (fun () -> ()) in
  let o =
    { opt_name = "--help"
    ; opt_short = Some "-h"
    ; opt_desc = "Print this help."
    ; opt_handle = NoArg !handle }
  in
  let c = { c with options = o::c.options } in
  handle := (fun () -> print_usage c);
  c

let cmd = Dynarray.create()

let add_command c =
  let c = add_help c in
  Dynarray.add_last cmd c;
  c

(*-------------------------------------------------------------------------*)
(** check command *)
(*-------------------------------------------------------------------------*)

let sign_of_path p =
  match !timeout with
  | None -> Handle.Compile.compile p
  | Some i ->
      try Lplib.Extra.timeout i Handle.Compile.compile p
      with Lplib.Extra.Timeout ->
        Common.Error.fatal_no_pos "timeout for checking %a." Common.Path.pp p

let compile file =
  sign_of_path (Common.Library.path_of_file Parsing.LpLexer.escape file)

let cmd_check =
  let summary = "Parse and type check the given files." in
  let c = add_command
            { name = "check"
            ; args = "[OPTION …] FILE …"
            ; summary
            ; desc = summary
            ; options = compile_options } in
  fun args ->
  match parse_options c.options args with
  | [] -> Common.Error.fatal_no_pos "no file provided"
  | f::files ->
      Parsing.Package.apply_config (Filename.dirname f);
      let time = Timed.Time.save() in
      ignore (compile f);
      let handle file =
        Timed.Time.restore time;
        Common.Console.reset_default();
        ignore (compile file)
      in
      List.iter handle files

(*-------------------------------------------------------------------------*)
(** decision-tree command *)
(*-------------------------------------------------------------------------*)

let ghost = ref false

let opt_ghost =
  { opt_name = "--ghost"
  ; opt_short = None
  ; opt_handle = NoArg(fun () -> ghost := true)
  ; opt_desc = "If NAME is a ghost symbol (e.g. ≡ for unification rules)." }

let cmd_dtree =
  let c = add_command
            { name = "decision-tree"
            ; args = "[OPTION …] MODULE.NAME"
            ; summary = "Print the decision tree of a symbol."
            ; desc =
{|Check MODULE and print to the standard output the decision tree of the
  symbol NAME in the Dot language. You can display it by piping this command
  to 'dot -Tpng | display'.|}
            ; options = opt_ghost :: compile_options } in
  fun args ->
  match parse_options c.options args with
  | [] -> Common.Error.fatal_no_pos "qualified identifier missing"
  | _::_::_ -> Common.Error.fatal_no_pos "too many arguments"
  | [s] ->
      let (p,id) as qid = parse_qident s in
      Parsing.Package.apply_config (Sys.getcwd());
      let sym =
        Timed.(Common.Console.verbose := 0);
        let sign = sign_of_path p in
        if !ghost then
          try Core.Sign.find Core.Sign.Ghost.sign id
          with Not_found ->
            Common.Error.fatal_no_pos "Unknown ghost symbol %s." id
        else
          try Core.Sig_state.find_sym ~prt:true ~prv:true
                (Core.Sig_state.of_sign sign) (Common.Pos.none qid)
          with Not_found ->
            Common.Error.fatal_no_pos "Unknown symbol %a.%s."
              Common.Path.pp p id
      in
      if Timed.(!(sym.Core.Term.sym_rules)) = [] then
        Common.Error.wrn None "symbol %s has no rule."
          sym.Core.Term.sym_name;
      Format.printf "%a" Tool.Tree_graphviz.to_dot sym

(*-------------------------------------------------------------------------*)
(** export command *)
(*-------------------------------------------------------------------------*)

type output = Lp | Dk | RawDk | Hrs | Xtc | RawCoq | SttCoq

let string_of_output = function
  | Lp -> "lp"
  | Dk -> "dk"
  | RawDk -> "raw_dk"
  | Hrs -> "hrs"
  | Xtc -> "xtc"
  | RawCoq -> "raw_coq"
  | SttCoq -> "stt_coq"

let output_of_string = function
  | "lp" -> Lp
  | "dk" -> Dk
  | "raw_dk" -> RawDk
  | "hrs" -> Hrs
  | "xtc" -> Xtc
  | "raw_coq" -> RawCoq
  | "stt_coq" -> SttCoq
  | s -> Common.Error.fatal_no_pos "invalid format: %s" s

let output = ref None

let check_output l =
  match !output with
  | None ->
      Common.Error.fatal_no_pos
        "the output format must be given before the other options"
  | Some o ->
      if not (List.mem o l) then
        Common.Error.fatal_no_pos "option invalid with format %s"
          (string_of_output o)

let opt_output =
  { opt_name = "--output"
  ; opt_short = Some "-o"
  ; opt_handle = Next("FMT", fun s -> output := Some(output_of_string s))
  ; opt_desc =
{|Specify the output language and how the input files must be interpreted.
  The possible formats are:
    lp: dk to lp translator, or lp code pretty-printer
    raw_dk: lp to dk syntactic translator (before elaboration)
    dk: lp to dk translator
    raw_coq: dk or lp to rocq syntactic translator (before elaboration)
    stt_coq: dk or lp to rocq syntactic translator (before elaboration)
    hrs: for checking the confluence of rewrite rules
    xtc: for checking the termination of rewrite rules|} }

let encoding = ref None

let opt_encoding =
  { opt_name = "--encoding="
  ; opt_short = None
  ; opt_handle = Suffix("FILE",
                        fun s -> check_output [SttCoq]; encoding := Some s)
  ; opt_desc =
{|Lambdapi file providing a list of builtins describing the symbols used for
  encoding simple type theory.|} }

let mapping = ref None

let opt_mapping =
  { opt_name = "--mapping="
  ; opt_short = None
  ; opt_handle = Suffix("FILE",
                        fun s -> check_output [SttCoq]; mapping := Some s)
  ; opt_desc =
{|Lambdapi file providing a list of builtins describing which Lambdapi symbol
  declarations must not be translated and by which expression each occurrence
  must be replaced.|} }

let requiring = ref None

let opt_requiring =
  { opt_name = "--requiring="
  ; opt_short = None
  ; opt_handle =
      Suffix("FILE",
             fun s -> check_output [SttCoq;RawCoq]; requiring := Some s)
  ; opt_desc =
{|Lambdapi modules to be required at the beginning of translated files.|} }

let renaming = ref None

let opt_renaming =
  { opt_name = "--renaming="
  ; opt_short = None
  ; opt_handle =
      Suffix("FILE",
             fun s -> check_output [SttCoq;RawCoq]; renaming := Some s)
  ; opt_desc =
{|Lambdapi file providing a list of builtins describing renamings to apply
  on identifiers.|} }

let opt_no_implicits =
  { opt_name = "--no-implicits"
  ; opt_short = None
  ; opt_handle = NoArg(fun () ->
                     check_output [SttCoq;RawCoq];
                     Export.Coq.use_implicits := false)
  ; opt_desc = "In case input symbols have no implicit arguments." }

let opt_use_notations =
  { opt_name = "--use-notations"
  ; opt_short = None
  ; opt_handle = NoArg(fun () ->
                     check_output [SttCoq;RawCoq];
                     Export.Coq.use_notations := true)
  ; opt_desc = "Generate Rocq code using notations for connectors." }

let export_options =
  opt_output
  :: opt_encoding
  :: opt_mapping
  :: opt_renaming
  :: opt_requiring
  :: opt_no_implicits
  :: opt_use_notations
  :: compile_options

let cmd_export =
  let c = add_command
            { name = "export"
            ; args = "-o FMT [OPTION …] FILE"
            ; summary = "Translate the given file to another format."
            ; desc =
{|Print on standard output a translation of FILE in the format FMT.|}
            ; options = export_options } in
  fun args ->
  match parse_options c.options args with
  | [] -> Common.Error.fatal_no_pos "no file provided"
  | _::_::_ ->
      Common.Error.fatal_no_pos
        "the export command accepts only one file as argument"
  | [file] ->
      let output =
        match !output with
        | None -> Common.Error.fatal_no_pos "no output format given"
        | Some o -> o
      in
      begin
        match output with
        | RawDk | Lp | SttCoq | RawCoq -> ()
        | _ -> Parsing.Package.apply_config (Filename.dirname file)
      end;
      let parse = Parsing.Parser.parse_file in
      match output with
      | Lp -> Parsing.Pretty.ast Format.std_formatter (parse file)
      | Dk -> Export.Dk.sign (compile file)
      | RawDk -> Export.Rawdk.print (parse file)
      | Hrs -> Export.Hrs.sign Format.std_formatter (compile file)
      | Xtc -> Export.Xtc.sign Format.std_formatter (compile file)
      | RawCoq ->
          Option.iter Export.Coq.set_renaming !renaming;
          Export.Coq.print (parse file)
      | SttCoq ->
          Export.Coq.stt := true;
          Option.iter Export.Coq.set_renaming !renaming;
          Option.iter Export.Coq.set_encoding !encoding;
          Option.iter Export.Coq.set_mapping !mapping;
          Option.iter Export.Coq.set_requiring !requiring;
          Export.Coq.print (parse file)

(*-------------------------------------------------------------------------*)
(** index command *)
(*-------------------------------------------------------------------------*)

let add = ref false

let opt_add =
  { opt_name = "--add"
  ; opt_short = None
  ; opt_handle = NoArg(fun () -> add := true)
  ; opt_desc = "Do not clear the index." }

let cmd_index =
  let summary = "Index the given files in a database." in
  let c = add_command
            { name = "index"
            ; args = "[OPTION …] FILE"
            ; summary
            ; desc = summary
            ; options = opt_add :: compile_options } in
  fun args ->
  match parse_options c.options args with
  | [] -> Common.Error.fatal_no_pos "no file provided"
  | files ->
  Tool.Indexing.load_rewriting_rules !rule_files;
  let time = Timed.Time.save() in
  let handle file =
    Timed.Time.restore time;
    Common.Console.reset_default();
    Tool.Indexing.index_sign (Common.Error.no_wrn compile file)
  in
  List.iter handle files

(*-------------------------------------------------------------------------*)
(** init command *)
(*-------------------------------------------------------------------------*)

let cmd_init =
  let summary = "Setup a new project directory." in
  let c = add_command
            { name = "init"
            ; args = "[OPTION …] MODPATH"
            ; summary
            ; desc = summary
            ; options = general_options } in
  fun args ->
  match parse_options c.options args with
  | [] -> Common.Error.fatal_no_pos "no module path provided"
  | _::_::_ -> Common.Error.fatal_no_pos "too many arguments"
  | [s] ->
      let root_path = parse_path s in
      (* Find out the package name, create the directory. *)
      let pkg_dir =
        match List.rev root_path with
        | []   -> assert false (* Unreachable. *)
        | s::_ -> s
      in
      if Sys.file_exists pkg_dir then
        Common.Error.fatal_no_pos "%s already exists." pkg_dir;
      Unix.mkdir pkg_dir 0o700;
      let write_file n pp =
        let oc = open_out n in
        let ppf = Format.formatter_of_out_channel oc in
        pp ppf; Format.pp_print_flush ppf (); close_out oc
      in
      (* Write the package configuration file. *)
      let pkg_file ppf =
        Format.fprintf ppf "package_name = %s@.root_path    = %a@."
          pkg_dir Common.Path.pp root_path
      in
      write_file (Filename.concat pkg_dir Parsing.Package.pkg_file) pkg_file;
      (* Write the Makefile and example file. *)
      let makefile ppf = Format.fprintf ppf
{|.POSIX:
.SUFFIXES:

SRC = $(wildcard *.lp)
OBJ = $(SRC:.lp=.lpo)

all: $(OBJ)

install: $(OBJ) lambdapi.pkg
	lambdapi install lambdapi.pkg $(OBJ) $(SRC)

uninstall:
	lambdapi uninstall lambdapi.pkg

clean:
	rm -f $(OBJ)

.lp.lpo:
	lambdapi check --gen-obj $<
|} in
      write_file (Filename.concat pkg_dir "Makefile") makefile

(*-------------------------------------------------------------------------*)
(** install command *)
(*-------------------------------------------------------------------------*)

let dry_run = ref false

let opt_dry_run =
  { opt_name = "--dry-run"
  ; opt_short = None
  ; opt_handle = NoArg(fun () -> dry_run := true)
  ; opt_desc =
{|Do not install anything, only print the command that would be
  executed if the option was not given.|} }

let cmd_install =
  let summary = "Install the given files." in
  let c = add_command
            { name = "init"
            ; args = "[OPTION …] [FILE …]"
            ; summary
            ; desc = summary
            ; options = opt_dry_run :: general_options } in
  fun args ->
  Install.run_install (*FIXME*)Config.default_config !dry_run
    (parse_options c.options args)

(*-------------------------------------------------------------------------*)
(** lsp command *)
(*-------------------------------------------------------------------------*)

let standard_lsp = ref false

let opt_standard_lsp =
  { opt_name = "--standard-lsp"
  ; opt_short = None
  ; opt_handle = NoArg(fun () -> standard_lsp := true)
  ; opt_desc =
{|Restrict to the standard LSP protocol, avoiding interactive proof
  support extensions that are not supported by all editors.|} }

let log_file = ref Lsp.Lp_lsp.default_log_file

let opt_log_file =
  { opt_name = "--log-file="
  ; opt_short = None
  ; opt_handle = Suffix("FILE", fun s -> log_file := s)
  ; opt_desc =
{|Use FILE as the log file for the LSP server
  (default is |}^Lsp.Lp_lsp.default_log_file^{|).|} }

let cmd_lsp =
  let summary = "Run an LSP server." in
  let c = add_command
            { name = "lsp"
            ; args = "[OPTION …]"
            ; summary
            ; desc = summary
            ; options = opt_standard_lsp::opt_log_file::general_options } in
  fun args ->
  match parse_options c.options args with
  | _::_ -> Common.Error.fatal_no_pos "invalid argument"
  | _ -> Lsp.Lp_lsp.main !standard_lsp !log_file

(*-------------------------------------------------------------------------*)
(** parse command *)
(*-------------------------------------------------------------------------*)

let cmd_parse =
  let summary = "Parse the given files." in
  let c = add_command
            { name = "parse"
            ; args = "[OPTION …] FILE …"
            ; summary
            ; desc = summary
            ; options = compile_options } in
  fun args ->
  match parse_options c.options args with
  | [] -> Common.Error.fatal_no_pos "no file provided"
  | files ->
      let handle file = ignore (Parsing.Parser.parse_file file) in
      List.iter handle files

(*-------------------------------------------------------------------------*)
(** search command *)
(*-------------------------------------------------------------------------*)

let require = ref None

let opt_require =
  { opt_name = "--require="
  ; opt_short = None
  ; opt_handle = Suffix("FILE", fun s -> require := Some s)
  ; opt_desc = "FILE to be required before starting the search." }

let cmd_search =
  let summary = "Query a database file." in
  let c = add_command
            { name = "search"
            ; args = "[OPTION …] QUERY"
            ; summary
            ; desc = summary
            ; options = compile_options } in
  fun args ->
  match parse_options c.options args with
  | [] -> Common.Error.fatal_no_pos "no query provided"
  | _::_::_ -> Common.Error.fatal_no_pos "too many arguments"
  | [s] ->
      Tool.Indexing.load_rewriting_rules !rule_files;
      let ss =
        match !require with
        | None -> Core.Sig_state.dummy
        | Some r ->
            Parsing.Package.apply_config (Filename.concat (Sys.getcwd()) r);
            Core.Sig_state.of_sign (sign_of_path (parse_path r))
      in
      let dbpath = !Tool.Indexing.the_dbpath in
      Printf.printf "%s" (Tool.Indexing.search_cmd_txt ss s ~dbpath)

(*-------------------------------------------------------------------------*)
(** uninstall command *)
(*-------------------------------------------------------------------------*)

let cmd_uninstall =
  let summary =
    "Uninstall the files corresponding to the given package file." in
  let _ = add_command
            { name = "init"
            ; args = "[OPTION …] FILE.pkg"
            ; summary
            ; desc = summary
            ; options = opt_dry_run :: general_options } in
  function
  | [] -> Common.Error.fatal_no_pos "no package file provided"
  | _::_::_ -> Common.Error.fatal_no_pos "too many arguments"
  | [s] ->
  Install.run_uninstall (*FIXME*)Config.default_config !dry_run s

(*-------------------------------------------------------------------------*)
(** websearch command *)
(*-------------------------------------------------------------------------*)

let header = ref None

let opt_header =
  { opt_name = "--header="
  ; opt_short = None
  ; opt_handle = Suffix("FILE", fun s -> header := Some s)
  ; opt_desc = "html file to use as header of the server web page." }

let url = ref ""

let opt_url =
  { opt_name = "--url="
  ; opt_short = None
  ; opt_handle = Suffix("STRING", fun s -> url := s)
  ; opt_desc = "Path prefixes accepted by the server." }

let port = ref 8080

let opt_port =
  { opt_name = "--port="
  ; opt_short = None
  ; opt_handle = Suffix("INT", fun s -> port := nat_of_string s)
  ; opt_desc = "Port used by the server (default is 8080)." }

let websearch_options =
  opt_require
  ::opt_header
  ::opt_url
  ::opt_port
  ::general_options

let cmd_websearch =
  let summary = "Start a webserver to search the index." in
  let c = add_command
            { name = "websearch"
            ; args = "[OPTION …]"
            ; summary
            ; desc = summary
            ; options = websearch_options } in
  fun args ->
  match parse_options c.options args with
  | _::_ -> Common.Error.fatal_no_pos "too many arguments"
  | [] ->
      Tool.Indexing.load_rewriting_rules !rule_files;
      let ss =
        match !require with
        | None -> Core.Sig_state.dummy
        | Some r ->
            Parsing.Package.apply_config (Filename.concat (Sys.getcwd()) r);
            Core.Sig_state.of_sign (sign_of_path (parse_path r))
      in
      let header =
        match !header with
        | None -> default_header
        | Some f -> Lplib.String.string_of_file f
      in
      let port = !port in
      let dbpath = !Tool.Indexing.the_dbpath in
      let path_in_url = !url in
      Tool.Websearch.start ~header ss ~port ~dbpath ~path_in_url ()

(*-------------------------------------------------------------------------*)
(** main procedure *)
(*-------------------------------------------------------------------------*)

let main = function
  | ["version"|"--version"] -> Printf.printf "%s\n" Core.Version.version
  | [] | ["help"|"-h"|"--help"] ->
      Printf.printf
{|%sUSAGE:%s lambdapi COMMAND [ARGUMENT …]

Do "lambdapi COMMAND -h" to get more information on each command.

%sCOMMANDS:%s

%shelp, -h, --help%s
  Provides this help.

%sversion, --version%s
  Prints the version of lambdapi.
 |} b r b r b r b r;
      for i = 0 to Dynarray.length cmd - 1 do
        Printf.printf
{|
%s%s%s
  %s
|} b (Dynarray.get cmd i).name r (Dynarray.get cmd i).summary
      done
  | "check"::args -> cmd_check args
  | "decision-tree"::args -> cmd_dtree args
  | "export"::args -> cmd_export args
  | "index"::args -> cmd_index args
  | "init"::args -> cmd_init args
  | "install"::args -> cmd_install args
  | "lsp"::args -> cmd_lsp args
  | "parse"::args -> cmd_parse args
  | "search"::args -> cmd_search args
  | "uninstall"::args -> cmd_uninstall args
  | "websearch"::args -> cmd_websearch args
  | s::_ -> Common.Error.fatal_no_pos "unknown command: %s" s

let _ =
  Common.Error.handle_exceptions
    (fun () -> main (List.tl (Array.to_list Sys.argv)))
