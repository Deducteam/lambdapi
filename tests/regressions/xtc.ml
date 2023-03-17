open Common
open Handle

let () =
  Library.set_lib_root (Some "/tmp");
  Timed.(Console.verbose := 0);
  let sign = Compile.PureUpToSign.compile_file "../OK/boolean.lp" in
  Export.Xtc.sign Format.std_formatter sign
