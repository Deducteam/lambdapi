open Lplib.Base
open Lplib.Extra

(** Printing functions. *)
module D = struct

  let ignore : 'a pp = fun _ _ -> ()

  let log_and_return logger el = logger el; el

  let log_and_raise logger exc = logger exc; raise exc

  let depth : int pp = fun ppf l ->
    for _i = 1 to l do out ppf " " done; out ppf "%d. " l

  let bool : bool pp = fun ppf b -> out ppf "%B" b

  let int : int pp = fun ppf i -> out ppf "%d" i

  let string : string pp = fun ppf s -> out ppf "%S" s

  let option : 'a pp -> 'a option pp = fun elt ppf o ->
    match o with
    | None -> out ppf "None"
    | Some x -> out ppf "Some(%a)" elt x

  let pair : 'a pp -> 'b pp -> ('a * 'b) pp = fun elt1 elt2 ppf (x1,x2) ->
    out ppf "%a,%a" elt1 x1 elt2 x2

  let list : 'a pp -> 'a list pp = fun elt ppf l ->
    match l with
    | [] -> out ppf "[]"
    | x::l ->
      out ppf "[%a" elt x;
      let f x = out ppf "; %a" elt x in
      List.iter f l;
      out ppf "]"

  let array : 'a pp -> 'a array pp = fun elt ppf a ->
    let n = Array.length a in
    if n = 0 then out ppf "[]"
    else begin
      out ppf "[%a" elt a.(0);
      for i = 1 to n-1 do out ppf "; %a" elt a.(i) done;
      out ppf "]"
    end

  let map : (('key -> 'elt -> unit) -> 'map -> unit)
    -> 'key pp -> string -> 'elt pp -> string -> 'map pp =
    fun iter key sep1 elt sep2 ppf m ->
    let f k t = out ppf "%a%s%a%s" key k sep1 elt t sep2 in
    out ppf "["; iter f m; out ppf "]"

  let strmap : 'a pp -> 'a StrMap.t pp = fun elt ->
    map StrMap.iter string ", " elt "; "

  let iter ?sep:(pp_sep = Format.pp_print_cut) iter pp_elt ppf v =
    let is_first = ref true in
    let pp_elt v =
      if !is_first then (is_first := false) else pp_sep ppf ();
      pp_elt ppf v
    in
    iter pp_elt v

  (* To be used in a hov (and not default) box *)
  let surround beg fin inside =
    fun fmt v -> Format.fprintf fmt "%s@;<0 2>@[<hv>%a@]@,%s" beg inside v fin

  let bracket inside = surround "[" "]" inside

end

(** Logging function for command handling. *)

(* The two successive let-bindings are necessary for type variable
   generalisation purposes *)
let log_hndl = Logger.make 'h' "hndl" "command handling"
let log_hndl = log_hndl.pp

(** To print time data. *)
let do_print_time = ref false

(** Print current time. *)
let print_time : string -> unit = fun s ->
  if !do_print_time && Logger.log_enabled () then
    log_hndl "@@%f %s" (Sys.time()) s

(** [time_of f x] computes [f x] and the time for computing it. *)
let time_of : (unit -> 'b) -> 'b = fun f ->
  if !do_print_time && Logger.log_enabled () then begin
    let t0 = Sys.time () in
    try f () |> D.log_and_return (fun _ -> log_hndl "%f" (Sys.time () -. t0))
    with e ->
      e |> D.log_and_raise  (fun _ -> log_hndl "%f" (Sys.time () -. t0))
  end else f ()
