constant symbol U : TYPE
injective symbol eU : U → TYPE
set flag "eta_equality" on // default is off
set flag "print_implicits" on // default is off
set flag "print_contexts" on // default is off
set flag "print_domains" on // default is off
set flag "print_meta_type" on // default is off
set debug +ui
definition trivial : Π A, eU A → eU A ≔ λB : U,( λ eA , eA)
