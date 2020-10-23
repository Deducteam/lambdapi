constant symbol B : TYPE
constant symbol b : B
set flag "eta_equality" on // default is off
set flag "print_implicits" on // default is off
set flag "print_contexts" on // default is off
set flag "print_domains" on // default is off
set flag "print_meta_type" on // default is off
set debug +ui
definition c : B ≔ let a ≔ b in a
