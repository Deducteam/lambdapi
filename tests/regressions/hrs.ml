(** HRS file generation *)
open Common

open Handle

let () =
  Library.set_lib_root (Some "/tmp");
  Timed.(Console.verbose := 0);
  let sign = Compile.Pure.compile_file "../OK/bool.lp" in
  Export.Hrs.to_HRS Format.std_formatter sign
