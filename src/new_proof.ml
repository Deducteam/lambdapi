(** Proofs and tactics. *)

open Timed
open Extra
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

(** [refine_goal ps t] attempts to instantiate the focused goal of [ps], using
    the given term [t]. New goals may be added to the goal list in the process
    if they are contained in [t]. *)
let refine_goal : t -> term -> t = fun ps t ->
  ignore (ps, t);
  assert false (* TODO *)

(** [finished ps] tells whether the proof represented by [ps] is finished. *)
let finished : t -> bool = fun ps -> ps.proof_goals = []

(** [pp oc ps] prints the proof state [ps] to channel [oc]. *)
let pp : t pp = fun oc ps ->
  Format.fprintf oc "== Current theorem ======================\n";
  let open Print in
  begin
    match ps.proof_goals with
    | []    -> Format.fprintf oc " No more goals...\n"
    | g::gs ->
        let print_hyp (s,(_,t)) =
          Format.fprintf oc "  %s : %a\n" s pp (Bindlib.unbox t)
        in
        List.iter print_hyp g.g_hyps;
        Format.fprintf oc " ----------------------------------------\n";
        Format.fprintf oc "  %a\n" pp g.g_type;
        if gs <> [] then
          begin
            Format.fprintf oc "\n";
            Format.fprintf oc " >0< %a : %a\n" pp_meta g.g_meta pp g.g_type;
            let print_goal i g =
              Format.fprintf oc " (%i) %a : %a\n" (i+1)
                pp_meta g.g_meta pp g.g_type
            in
            List.iteri print_goal gs
          end
  end;
  Format.fprintf oc "==========================================\n"
