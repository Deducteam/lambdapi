open Common
open Handle

let () =
  Library.set_lib_root (Some "/tmp");
  Timed.(Console.verbose := 0);
  let sign = Compile.pure_compile_file "../OK/bool.lp" in
  Export.Xtc.to_XTC Format.std_formatter sign
