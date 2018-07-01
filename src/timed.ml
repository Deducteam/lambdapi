module Time =
  struct
    type t = T : {mutable p : t option; r : 'a ref; mutable v : 'a} -> t

    let current : t ref =
      ref (T {p = None; r = ref 0; v = 0})

    let save : unit -> t = fun () -> !current

    let rollback : t -> unit =
      let rec fn acc time =
        match time with
        | T {p = Some t} -> fn (time::acc) t
        | _              -> gn acc time
      and gn acc (T r as t0) =
        let v = r.v in
        r.v <- !(r.r);
        r.r := v;
        match acc with
        | []     -> r.p <- None; current := t0
        | t::acc -> r.p <- Some t; gn acc t
      in
      fn []
  end

let (:=) : 'a ref -> 'a -> unit = fun r v ->
  let open Time in
  let node = T {p = None; r; v = !r} in
  match !current with T n -> n.p <- Some node; current := node; r := v

let incr : int ref -> unit = fun r -> r := !r + 1
let decr : int ref -> unit = fun r -> r := !r - 1

let pure_apply : ('a -> 'b) -> 'a -> 'b = fun f v ->
  let t = Time.save () in
  let r = f v in
  Time.rollback t; r

let pure_test : ('a -> bool) -> 'a -> bool = fun f v ->
  let t = Time.save () in
  let r = f v in
  if not r then Time.rollback t; r
