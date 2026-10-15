(* Borne de Hadamard/cofacteurs pour un générateur extrémal entier du cône
   {lambda >= 0 | A^T lambda = 0}. Tout générateur extrémal a un support
   minimal de taille <= n+1; ses coordonnées sont des mineurs d'ordre <= n,
   donc <= n! M^n, où M borne les coefficients de A. *)
let coefficient_bound constraints =
  let n =
    if Array.length constraints = 0 then 0
    else Array.length constraints.(0).Checker.coefficients
  in
  let m =
    Array.fold_left
      (fun acc c ->
        Array.fold_left
          (fun acc x -> max acc (abs x))
          acc c.Checker.coefficients)
      0 constraints
  in
  let bound = ref 1 in
  for k = 1 to n do
    bound := !bound * k;
    bound := !bound * (max 1 m)
  done;
  !bound

let find constraints =
  let rows = Array.length constraints in
  if rows = 0 then None
  else begin
    let bound = coefficient_bound constraints in
    let values = Array.make rows 0 in
    let rec visit i =
      if i = rows then
        let cert = { Checker.multipliers = Array.copy values } in
        try
          Checker.check constraints cert;
          Some cert
        with Checker.Invalid_certificate _ -> None
      else
        let rec try_value v =
          if v > bound then None
          else begin
            values.(i) <- v;
            match visit (i + 1) with
            | Some _ as found -> found
            | None -> try_value (v+1)
          end
        in
        try_value 0
    in
    visit 0
  end
