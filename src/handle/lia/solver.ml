open Lplib open Base

type constraint_line = {
  coeffs : int array; (* coeffs of variables *)
  const : int; (* additional constant *)
  history: (int * int) list; (* computed multiplier *)
}

(** [gcd n m] Computes the greatest common divisor of [n] and [m]
    using Euclid's algorithm *)
let gcd: int -> int -> int =
  fun a b ->
  let rec loop x y = if y = 0 then abs x else loop y (x mod y) in
  loop a b

(** Computes the global GCD of an array of coefficients and a constant term.
    If the array is empty, returns 1.
 *)
let gcd_array: int array -> int -> int =
  fun arr const ->
  let g = Array.fold_left gcd 0 arr in
  if Array.length arr = 0 then 1 else gcd g const

(** Simplifies a constraint line by dividing all its numbers by
    their global GCD *)
let simplify_line: constraint_line -> constraint_line =
  fun line ->
  let g = gcd_array line.coeffs line.const in
  if g > 1 then
    (* Check if g perfectly divides all weights in the history to maintain
       integer precision *)
    let can_divide_history =
      List.for_all (fun (w, _) -> w mod g = 0) line.history in
    if can_divide_history then
      { coeffs = Array.map (fun c -> c / g) line.coeffs;
        const = line.const / g;
        history = List.map (fun (w, idx) -> (w / g, idx)) line.history }
    else line
  else line

(** Detects a mathematical contradiction: 0 * x + b <= 0 where b > 0 *)
let detect_contradiction: constraint_line -> (int * int) list option =
  fun line ->
  let all_zero = Array.for_all (fun c -> c = 0) line.coeffs in
  if all_zero && line.const > 0 then Some line.history else None

(** Combines an upper bound and a lower bound constraint to eliminate
    the variable at index 0 *)
let combine: constraint_line -> constraint_line -> constraint_line =
  fun line_inf line_sup ->
  if Array.length line_inf.coeffs = 0 || Array.length line_sup.coeffs = 0 then
    failwith "Dimension error: empty coefficient array";
  let c_inf = line_inf.coeffs.(0) in
  let c_sup = line_sup.coeffs.(0) in
  let w_inf = - c_sup in
  let w_sup = c_inf in
  let n = Array.length line_inf.coeffs in
  let new_coeffs = Array.init (n - 1) (fun i ->
      w_inf * line_inf.coeffs.(i + 1) + w_sup * line_sup.coeffs.(i + 1)
    ) in
  let new_const = w_inf * line_inf.const + w_sup * line_sup.const in
  let h_inf = List.map (fun (w, idx) -> (w * w_inf, idx)) line_inf.history in
  let h_sup = List.map (fun (w, idx) -> (w * w_sup, idx)) line_sup.history in
  simplify_line {
    coeffs = new_coeffs; const = new_const; history = h_inf @ h_sup }

(** Partition constraints according to the sign of their first coefficient
    and eliminates it *)
let eliminate_one_variable: constraint_line list -> constraint_line list =
  fun constraints ->
  let pos, neg, zero = List.fold_left (fun (p, n, z) line ->
      if Array.length line.coeffs = 0 then (p, n, line::z)
      else
        let c = line.coeffs.(0) in
        let r = Array.sub line.coeffs 1 (Array.length line.coeffs - 1) in
        if c > 0 then (line::p, n, z)
        else if c < 0 then (p, line::n, z)
        else ({ line with coeffs = r }::p, n, { line with coeffs = r }::z)
    ) ([], [], []) constraints in
  if pos = [] || neg = [] then
    let strip_first l =
      if Array.length l.coeffs = 0 then l
      else { l with coeffs = Array.sub l.coeffs 1 (Array.length l.coeffs-1) }
    in
    List.map strip_first zero
  else
    let combined =
      List.fold_left (fun acc l_inf ->
          List.fold_left (fun acc_inner l_sup ->
              combine l_inf l_sup :: acc_inner
            ) acc neg
        ) [] pos
    in
    zero @ combined

(** Recursively applies Fourier-Motzkin elimination to find a
    contradiction certificate *)
let rec find_certificate: constraint_line list -> (int * int) list option =
  fun constraints ->
  let rec check_all = function
    | [] -> None
    | l :: q -> match detect_contradiction l with
      | Some h -> Some h
      | None -> check_all q
  in
  match check_all constraints with
  | Some cert -> Some cert
  | None ->
    let has_variables = List.exists (fun l -> Array.length l.coeffs <> 0)
        constraints in
    if not has_variables then None
    else find_certificate (eliminate_one_variable constraints)

(** Solves a system of inequalities Ax + b <= 0. Returns an array of weights
    if unsatisfiable, or None *)
let solve_system: (int array * int) list -> int array option =
  fun raw_constraints ->
  let num_constraints = List.length raw_constraints in
  let initial_constraints = List.mapi (fun idx (coeffs, const) ->
      simplify_line { coeffs; const; history = [(1, idx)] }
    ) raw_constraints in
  match find_certificate initial_constraints with
  | None -> None
  | Some raw_cert ->
    let weights_array = Array.make num_constraints 0 in
    List.iter (fun (w, idx) ->
        weights_array.(idx) <- weights_array.(idx) + w
      ) raw_cert;
    (* Scale down the weights by their global GCD to get the minimal
       integer certificate *)
    let total_gcd = Array.fold_left gcd 0 weights_array in
    if total_gcd > 1 then
      Some (Array.map (fun w -> w / total_gcd) weights_array)
    else
      Some weights_array

(* pretty printers *)
module PRT = struct
  (* a constraint line *)
  let cl = fun ppf v ->
    out ppf "[%a] + %d <= 0" (Array.pp Base.int ",") v.coeffs v.const

  (* a list of constraint lines *)
  let cls = fun ppf v -> out ppf "[%a]" (List.pp cl "; ") v

  (* a constraint *)
  let ct = fun ppf (k,c) ->
    out ppf "[%a] + %d <= 0" (Array.pp Base.int ",") k c

  (* a list of constraints *)
  let ctl = fun ppf lc ->
    out ppf "%a" (List.pp ct "; ") lc
end
