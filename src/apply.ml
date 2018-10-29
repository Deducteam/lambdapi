open Basics
open Console
open Terms
open Refine

(** [nbArgsOf t] counts the number of arguments of the type [t], i.e.
    it counts the number of Prod binders located at the front of [t]. *)
let rec nbArgsOf : term -> int = fun t ->
  match unfold t with
  | Prod(_,b)   -> let (_,b) = Bindlib.unbind b in 1 + nbArgsOf b
  | _   -> 0  

  (** [handle_apply t pos ps] tries to apply the apply tactic (done on 
    line [pos]) to the proof state [ps], and returns the new proof state. *)
let handle_apply : term -> Pos.popt -> Proof.t -> Proof.t = 
  fun t pos ps ->
  let (g, _) =
    match Proof.(ps.proof_goals) with
    | []    -> fatal pos "There is nothing left to prove.";
    | g::gs -> (g, gs)
  in
  let (env, _) = Proof.Goal.get_type g in
  let ctx = Ctxt.of_env env in
  let t_type = match Solve.infer ctx t with
  | Some(a) -> a
  | None    -> fatal pos "Cannot infer the type of [%a]." Print.pp t
  in
  let nbProd = nbArgsOf t_type in
  (* Note that nbProd can be zero, so apply can be used as an exact *)
  let t = add_args t (List.init nbProd (fun _ -> Wild)) in
  handle_refine t pos ps
