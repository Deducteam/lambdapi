open Common
open Handle

let () =
  Library.set_lib_root (Some "/tmp");
  Timed.(Console.verbose := 0);
  let sign = Compile.Pure.compile_file "../OK/bool.lp" in
  Tool.Xtc.to_XTC Format.std_formatter sign
