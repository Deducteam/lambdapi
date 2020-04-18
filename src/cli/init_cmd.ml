open Cmdliner
open Core
open Console
open Files

let with_file : string -> (out_channel -> unit) -> unit = fun file fn ->
  let oc = open_out file in fn oc; close_out oc

let write_makefile : out_channel -> unit = fun oc ->
  let lines =
    [ "LP_SRC = $(shell find . -type f -name \"*.lp\")"
    ; "LP_OBJ = $(LP_SRC:%.lp=%.lpo)"
    ; ""
    ; "all: $(LP_OBJ)"
    ; ""
    ; "$(LP_OBJ)&: $(LP_SRC)"
    ; "\tlambdapi check --gen-obj $^"
    ; ""
    ; "install: $(LP_OBJ) " ^ Package.pkg_file
    ; "\tlambdapi install " ^ Package.pkg_file ^ " $(LP_OBJ) $(LP_SRC)"
    ; ""
    ; "uninstall:"
    ; "\tlambdapi uninstall lambdapi.pkg"
    ; ""
    ; "clean:"
    ; "\trm -f $(LP_OBJ)" ]
  in
  List.iter (Printf.fprintf oc "%s\n") lines

let write_ex_nat : out_channel -> unit = fun oc ->
  let lines =
    [ "// Generated example file: unary natural numbers."
    ; "constant symbol N : TYPE"
    ; ""
    ; "constant symbol z : N"
    ; "constant symbol s : N → N"
    ; ""
    ; "// Enabling built-in natural number literal, and example."
    ; ""
    ; "set builtin \"0\"  ≔ z"
    ; "set builtin \"+1\" ≔ s"
    ; ""
    ; "definition forty_two ≔ 42"
    ; ""
    ; "// Addition function."
    ; ""
    ; "symbol add : N → N → N"
    ; "set infix left 6 \"+\" ≔ add"
    ; ""
    ; "rule z      + $n     ↪ $n"
    ; "with (s $m) + $n     ↪ s ($m + $n)"
    ; "with $m     + z      ↪ $m"
    ; "with $m     + (s $n) ↪ s ($m + $n)" ]
  in
  List.iter (Printf.fprintf oc "%s\n") lines

let write_ex_main : Path.t -> out_channel -> unit = fun root_path oc ->
  let lines =
    let mp = String.concat "." root_path in
    [ "// Generated example file."
    ; "require open " ^ mp ^ ".nat // Note the full module qualification."
    ; ""
    ; "assert 42 + 12 ≡ 54" ]
  in
  List.iter (Printf.fprintf oc "%s\n") lines

let run : Path.t -> unit = fun root_path ->
  let run _ =
    (* Make sure that the module path is well-formed. *)
    Path.check_simple root_path;
    (* Find out the package name, create the directory. *)
    let pkg_name =
      match List.rev root_path with
      | []   -> assert false (* Unreachable. *)
      | s::_ -> s
    in
    if Sys.file_exists pkg_name then
      fatal_no_pos "Cannot create the package: [%s] already exists." pkg_name;
    Unix.mkdir pkg_name 0o700;
    (* Write the package configuration file. *)
    let write_pkg_file oc =
      Printf.fprintf oc "package_name = %s\n" pkg_name;
      Printf.fprintf oc "root_path    = %s\n" (String.concat "." root_path)
    in
    let pkg_file = Filename.concat pkg_name Package.pkg_file in
    with_file pkg_file write_pkg_file;
    (* Write the Makefile and example file. *)
    with_file (Filename.concat pkg_name "Makefile") write_makefile;
    with_file (Filename.concat pkg_name "nat.lp") write_ex_nat;
    with_file (Filename.concat pkg_name "main.lp") (write_ex_main root_path)
  in
  Console.handle_exceptions run

let root_path : Path.t Term.t =
  let doc =
    "Defines the root path of the package. It is the module path under which \
     the package will be registered and installed (if desired), and it will \
     hence uniquely identify the package. In particular, the last identifier \
     that constitutes $(docv) will be used as package name. It is important \
     to note that the module of the package will always be accessed through \
     their qualified form, which is will be prefixed by $(docv). Refer to \
     the documentation for more information on the module system."
  in
  let i = Arg.(info [] ~docv:"MOD_PATH" ~doc) in
  Arg.(non_empty & pos 0 (list ~sep:'.' string) [] & i)


let cmd =
  let doc = "Create a new Lambdapi package to get started with a project." in
  Term.(const run $ root_path),
  Term.info "init" ~doc
