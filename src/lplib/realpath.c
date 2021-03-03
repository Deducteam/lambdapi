#include <limits.h>
#include <stdlib.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/fail.h>

CAMLprim value c_realpath(value v) {
  // Conversion of the argument to a C value, and performing the C call.
  const char *input_path = String_val(v);
  char *output_path = realpath(input_path, NULL);

  // Checking for error.
  if (output_path == NULL)
    caml_invalid_argument("Filename.realpath\0");

  // Preparing the result value.
  value res = caml_copy_string(output_path);

  // Free the memory allocated by [realpath] before returning.
  free(output_path);
  return res;
}
