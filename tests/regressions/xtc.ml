open Common
open Handle

let () =
  Library.set_lib_root (Some "/tmp");
  Timed.(Console.verbose := 0);
  let sign = Library.restore_after Compile.compile_file "../OK/group.lp" in
  Export.Xtc.sign Format.std_formatter sign
