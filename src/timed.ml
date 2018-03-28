module Time =
  struct
    type t = { mutable next : t option ; undo : unit -> unit }

    let current : t ref =
      ref { next = None ; undo = (fun () -> ()) }

    let save : unit -> t = fun () -> !current

    let rollback : t -> unit = fun t ->
      let rec fn = function
        | None   -> ()
        | Some t -> t.undo (); fn t.next; t.next <- None
      in fn t.next; t.next <- None; current := t
  end

let (:=) : 'a ref -> 'a -> unit = fun r v ->
  let open Time in
  let v0 = !r in
  let t = { next = None; undo = (fun () -> r := v0) } in
  !current.next <- Some t; current := t; r := v

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
