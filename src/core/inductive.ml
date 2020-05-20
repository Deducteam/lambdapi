open Timed
open Terms

let principle : sym -> sym list -> term = fun head _ -> (* @WIP *)
  !(head.sym_type)
