(* query language *)
type side = Lhs | Rhs
type inside = Exact | Inside
type 'inside where =
 | Spine of 'inside
 | Conclusion of 'inside
 | Hypothesis of 'inside
type constr =
 | QType of (inside option) where option
 | QXhs  of inside option * side option
type base_query =
 | QName of string
 | QSearch of Syntax.p_term * (*generalize:*)bool * constr option
type op =
 | Intersect
 | Union
type filter =
 | Path of string
 | RegExp of Str.regexp
type query =
 | QBase of base_query
 | QOpp of query * op * query
 | QFilter of query * filter
