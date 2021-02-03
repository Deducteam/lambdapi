open Core
open Cmdliner
open Common
open Console
open Module

let with_file : string -> (out_channel -> unit) -> unit = fun file fn ->
  let oc = open_out file in fn oc; close_out oc

let write_makefile : out_channel -> unit = fun oc ->
  Printf.fprintf oc
    ".POSIX:\n\
     SRC = nat.lp main.lp\n\
     OBJ = $(SRC:.lp=.lpo)\n\
     .SUFFIXES:\n\
     \n\
     all: $(OBJ)\n\
     \n\
     install: $(OBJ) %s\n\
     \tlambdapi install %s $(OBJ) $(SRC)\n\
     \n\
     uninstall:\n\
     \tlambdapi uninstall lambdapi.pkg\n\
     \n\
     clean:\n\
     \trm -f $(OBJ)\n\
     \n\
     .SUFFIXES: .lp .lpo\n\
     \n\
     .lp.lpo:\n\
     \tlambdapi check --gen-obj $<\n%!" Package.pkg_file Package.pkg_file

let write_ex_nat : out_channel -> unit = fun oc ->
  Printf.fprintf oc
    "// Generated example file: unary natural numbers.\n\
     constant symbol N : TYPE\n\
     \n\
     constant symbol z : N\n\
     constant symbol s : N → N\n\
     \n\
     // Enabling built-in natural number literal, and example.\n\
     \n\
     set builtin \"0\"  ≔ z\n\
     set builtin \"+1\" ≔ s\n\
     \n\
     definition forty_two ≔ 42\n\
     \n\
     // Addition function.\n\
     \n\
     symbol add : N → N → N\n\
     set infix left 6 \"+\" ≔ add\n\
     \n\
     rule z      + $n     ↪ $n\n\
     with (s $m) + $n     ↪ s ($m + $n)\n\
     with $m     + z      ↪ $m\n\
     with $m     + (s $n) ↪ s ($m + $n)\n%!"

let write_ex_main : Path.t -> out_channel -> unit = fun root_path oc ->
  Printf.fprintf oc
    "// Generated example file.\n\
     require open %s.nat // Note the full module qualification.\n\
     \n\
     assert 42 + 12 ≡ 54\n%!" (String.concat "." root_path)

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
     to note that the files of the package can be accessed only through \
     their qualified form prefixed by $(docv). Refer to \
     the documentation for more information on the module system."
  in
  let i = Arg.(info [] ~docv:"MOD_PATH" ~doc) in
  Arg.(non_empty & pos 0 (list ~sep:'.' string) [] & i)


let cmd =
  let doc = "Create a new Lambdapi package to get started with a project." in
  Term.(const run $ root_path),
  Term.info "init" ~doc
