module Time =
  struct
    type edge = E : {mutable d : node; r : 'a ref; mutable v : 'a} -> edge
    and  node = {mutable e : edge option}

    let reverse : node -> unit = fun ({e} as s) ->
      match e with
      | None                         -> assert false
      | Some(E ({d;r;v} as rc) as e) ->
          (* Undo the reference. *)
          rc.v <- !r; r := v;
          (* Reverse the pointers. *)
          d.e <- Some e; rc.d <- s

    type t = node

    let current : t ref = ref {e = None}

    let save : unit -> t =
      fun () -> !current

    let restore : t -> unit =
      let rec gn acc t0 =
        match acc with
        | []     -> current := t0; t0.e <- None
        | t::acc -> reverse t; gn acc t
      in
      let rec fn acc ({e} as time) =
        match e with
        | None        -> gn acc time
        | Some(E {d}) -> fn (time::acc) d
      in
      fn []
  end

let (:=) : 'a ref -> 'a -> unit = fun r v ->
  let open Time in
  let n = {e = None} in
  let e = E {d = n; r; v = !r} in
  !current.e <- Some e; current := n; r := v

let incr : int ref -> unit = fun r -> r := !r + 1
let decr : int ref -> unit = fun r -> r := !r - 1

let pure_apply : ('a -> 'b) -> 'a -> 'b = fun f v ->
  let t = Time.save () in
  let r = f v in
  Time.restore t; r

let pure_test : ('a -> bool) -> 'a -> bool = fun f v ->
  let t = Time.save () in
  let r = f v in
  if not r then Time.restore t; r
