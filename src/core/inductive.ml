open Timed
open Terms

type inductive =
  { ind_constructors : sym list   ; (** the list of constructors           *)
    ind_prop         : sym option ; (** one inductive principle (Prop one) *) }

let principle : sym -> sym list -> term = fun head _ -> (* @WIP *)
  !(head.sym_type)
