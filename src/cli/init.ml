open Cmdliner
open Common open Error
open Format
open Parsing

module CLT = Cmdliner.Term

let write_file : string -> (formatter -> unit) -> unit = fun fn pp ->
  let oc = open_out fn in
  let ppf = formatter_of_out_channel oc in
  pp ppf; pp_print_flush ppf (); close_out oc

let makefile : formatter -> unit = fun ppf ->
  fprintf ppf "\
.POSIX:
SRC =
OBJ = $(SRC:.lp=.lpo)
.SUFFIXES:

all: $(OBJ)

install: $(OBJ) %s
	lambdapi install %s $(OBJ) $(SRC)

uninstall:
	lambdapi uninstall lambdapi.pkg

clean:
	rm -f $(OBJ)

.SUFFIXES: .lp .lpo

.lp.lpo:
	lambdapi check --gen-obj $<@." Package.pkg_file Package.pkg_file

let run : Path.t -> unit = fun root_path ->
  let run _ =
    (* Find out the package name, create the directory. *)
    let pkg_name =
      match List.rev root_path with
      | []   -> assert false (* Unreachable. *)
      | s::_ -> s
    in
    if Sys.file_exists pkg_name then
      fatal_no_pos "Cannot create the package: \"%s\" already exists."
        pkg_name;
    Unix.mkdir pkg_name 0o700;
    (* Write the package configuration file. *)
    let pkg_file ppf =
      fprintf ppf "package_name = %s@.root_path    = %a@."
        pkg_name Path.pp root_path
    in
    write_file (Filename.concat pkg_name Package.pkg_file) pkg_file;
    (* Write the Makefile and example file. *)
    write_file (Filename.concat pkg_name "Makefile") makefile;
  in
  Error.handle_exceptions run

let root_path : Path.t CLT.t =
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
  Cmd.v (Cmd.info "init" ~doc) Cmdliner.Term.(const run $ root_path)
