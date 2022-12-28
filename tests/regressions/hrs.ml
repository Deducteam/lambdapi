(** HRS file generation *)

open Common
open Handle

let () =
  Library.set_lib_root (Some "/tmp");
  Timed.(Console.verbose := 0);
  let sign = Compile.PureUpToSign.compile_file "../OK/bool.lp" in
  Export.Hrs.sign Format.std_formatter sign
