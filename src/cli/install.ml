open Cmdliner
open Common open Library open Error
open Parsing

let run_command : bool -> string -> unit = fun dry_run cmd ->
  if dry_run then Console.out 1 "%s" cmd else
  match Sys.command cmd with
  | 0 -> ()
  | _ -> fatal_no_pos "Command [%s] failed." cmd
  | exception Failure(msg) ->
      fatal_msg "Command [%s] failed." cmd;
      fatal_no_pos "Reported error: %s." msg

let run_install : Config.t -> bool -> string list -> unit =
    fun cfg dry_run files ->
  let run _ =
    let open Timed in
    Config.init cfg;
    let time = Time.save () in
    let install file =
      Time.restore time;
      let dest =
        if Filename.basename file = Package.pkg_file then
          begin
            (* Install package file at the root path. *)
            let path = Package.((read file).root_path) in
            let lib_root =
              match Stdlib.(!lib_root) with
              | None -> assert false
              | Some(p) -> p
            in
            let dir = List.fold_left Filename.concat lib_root path in
            Filename.concat dir Package.pkg_file
          end
        else
          begin
            (* Source or object file, find out expected destination. *)
            Package.apply_config file;
            Library.install_path file
          end
      in
      (* Create directories as needed for [dest]. *)
      let cmd =
        let dest_dir = Filename.dirname dest in
        String.concat " " ["mkdir"; "--parents"; dest_dir]
      in
      run_command dry_run cmd;
      (* Copy files. *)
      let cmd =
        let file = Filename.quote file in
        String.concat " "
          ["cp"; "--preserve"; "--no-target-directory"; "--force"; file; dest]
      in
      run_command dry_run cmd
    in
    List.iter install files
  in
  Error.handle_exceptions run

let run_uninstall : Config.t -> bool -> string -> unit =
    fun cfg dry_run pkg_file ->
  let run _ =
    Config.init cfg;
    (* Read the package configuration file for the package to uninstall. *)
    let (pkg_name, pkg_root_path) =
      let pkg_config = Package.read pkg_file in
      Package.(pkg_config.package_name, pkg_config.root_path)
    in
    (* Compute the expected installation directory. *)
    let lib_root = match !lib_root with None -> assert false | Some(p) -> p in
    let pkg_dir = List.fold_left Filename.concat lib_root pkg_root_path in
    let pkg_file = Filename.concat pkg_dir Package.pkg_file in
    (* Check that a package is indeed installed there. *)
    if not (Sys.file_exists pkg_file) then
      fatal_no_pos "Specified package is not installed.";
    (* Check that the installed package has the expected name. *)
    let installed_name = Package.((read pkg_file).package_name) in
    if pkg_name <> installed_name then
      fatal_no_pos "Unexpected package [%s] installed under the same \
                    root path intended for specified package [%s]."
        installed_name pkg_name;
    (* Do the actual uninstallation. *)
    let cmd = "rm -r " ^ Filename.quote pkg_dir in
    run_command dry_run cmd
  in
  Error.handle_exceptions run

let dry_run : bool Term.t =
  let doc =
    "Do not install anything, only print the command that would be executed \
     if the option was not given."
  in
  Arg.(value & flag & info ["dry-run"] ~doc)

let pkg_file : string Term.t =
  let doc =
    Printf.sprintf
      "Path to the package configuration file $(b,%s) corresponding to the \
       package that should be uninstalled." Package.pkg_file
  in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"FILE" ~doc)

let files : string list Term.t =
  let doc =
    Printf.sprintf
      "Source file with the [%s] extension (or with the [%s] extension when \
       using the Dedukti syntax), object file with the [%s] extension,
       or package configuration file $(b,%s)."
       lp_src_extension dk_src_extension obj_extension Package.pkg_file
  in
  Arg.(value & (pos_all non_dir_file []) & info [] ~docv:"FILE" ~doc)

let install_cmd =
  let doc = "Install the given files under the library root." in
  Term.(const run_install $ Config.minimal $ dry_run $ files),
  Term.info "install" ~doc

let uninstall_cmd =
  let doc = "Uninstall the files corresponding to the given package file." in
  Term.(const run_uninstall $ Config.minimal $ dry_run $ pkg_file),
  Term.info "uninstall" ~doc
