(** Proofs and tactics. *)

open Timed
open Pos
open Terms
open Console

(** Representation of a goal. *)
type goal =
  { g_meta : meta  (** Metavariable that needs to be instantiated.          *)
  ; g_hyps : Env.t (** Precomputed environment from the domain of its type. *)
  ; g_type : term  (** Precomputed codomain of its type. *) }

(** Representation of the state of the proof of a theorem. *)
type proof =
  { proof_name  : Pos.strloc (** Name of the proved theorem.            *)
  ; proof_term  : meta       (** Metavariable holding the proof term.   *)
  ; proof_goals : goal list  (** List of open goals (focused is first). *) }

(** Short synonym for qualified use. *)
type t = proof

(** [init id a] returns an initial proof state for a theorem named [id], which
    statement is represented by the type [a]. *)
let init : Pos.strloc -> term -> t = fun ({elt=id} as proof_name) a ->
  let proof_term = fresh_meta ~name:id a 0 in
  let proof_goals = [{g_meta = proof_term; g_hyps = []; g_type = a}] in
  { proof_name ; proof_term ; proof_goals }

(** [finished ps] tells whether the proof represented by [ps] is finished. *)
let finished : t -> bool = fun ps -> ps.proof_goals = []
