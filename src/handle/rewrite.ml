(** Implementation of the rewrite tactic. *)

open Lplib
open Common open Pos open Error open Debug
open Core open Term open Print
open Goal

(** Logging function for the rewrite tactic. *)
let log = Logger.make 'r' "rtac" "rewrite tactic"
let log = log.pp

(** Equality configuration. *)
type eq_config =
  { symb_P     : sym (** Encoding of propositions.        *)
  ; symb_T     : sym (** Encoding of types.               *)
  ; symb_eq    : sym (** Equality proposition.            *)
  ; symb_eqind : sym (** Induction principle on equality. *)
  ; symb_refl  : sym (** Reflexivity of equality.         *) }

(** Additional configuration needed only when rewrite has to lift an equality
    over a binder. *)
type binder_rewrite_config =
  { symb_arr    : sym (** HOL non-dependent function type constructor. *)
  ; symb_funext : sym (** Functional extensionality principle.        *) }

(** [get_eq_config ss pos] returns the current configuration for
    equality, used by tactics such as “rewrite” or “reflexivity”. *)
let get_eq_config : Sig_state.t -> popt -> eq_config = fun ss pos ->
  let builtin = Builtin.get ss pos [] in
  { symb_P     = builtin "Prf"
  ; symb_T     = builtin "El"
  ; symb_eq    = builtin "eq"
  ; symb_eqind = builtin "eqind"
  ; symb_refl  = builtin "refl" }

(** [get_binder_rewrite_config ss pos] returns the configuration needed for
    binder-dependent rewrite occurrences. *)
let get_binder_rewrite_config :
    Sig_state.t -> popt -> binder_rewrite_config = fun ss pos ->
  let builtin = Builtin.get ss pos [] in
  { symb_arr    = builtin "arr"
  ; symb_funext = builtin "funExt" }

(** [get_eq_data pos cfg a] returns [((a,l,r),[v1;..;vn])] if [a ≡ Π v1:A1,
   .., Π vn:An, P (eq a l r)] and fails otherwise. *)
let get_eq_data :
  eq_config -> popt -> term -> (term * term * term) * var list = fun cfg ->
  let exception Not_eq of term in
  let get_eq_args u =
    if Logger.log_enabled () then log "get_eq_args %a" term u;
    match get_args u with
    | eq, [a;l;r] when is_symb cfg.symb_eq eq -> a, l, r
    | _ -> raise (Not_eq u)
  in
  let exception Not_P of term in
  let return vs r = r, List.rev vs in
  let rec get_eq vs t notin_whnf =
    if Logger.log_enabled () then log "get_eq %a" term t;
    match get_args t with
    | Prod(_,t), _ ->
        (* We prefix variable names by "$" to distinguish them from the
           variables occurring in other assumptions or in the goal, and
           because we will try to match them with some subterm of the goal. *)
        let v,t = unbind ~name:("$"^binder_name t) t in get_eq (v::vs) t true
    | p, [u] when is_symb cfg.symb_P p ->
      begin
        let u = Eval.whnf ~tags:[NoRw;NoExpand] [] u in
        try return vs (get_eq_args u)
        with Not_eq _ ->
          (try return vs (get_eq_args (Eval.whnf [] u))
           with Not_eq _ when notin_whnf -> get_eq vs (Eval.whnf [] t) false)
      end
    | _ ->
      if notin_whnf then get_eq vs (Eval.whnf [] t) false
      else raise (Not_P t)
  in
  fun pos t ->
    if Logger.log_enabled () then log "get_eq_data %a" term t;
    try get_eq [] t true with
    | Not_P u ->
      fatal pos "Expected %a _ but found %a." sym cfg.symb_P term u
    | Not_eq u ->
      fatal pos "Expected %a _ _ but found %a." sym cfg.symb_eq term u

(** Type of a term with the free variables that need to be substituted. It is
   usually used to store the LHS of a proof of equality, together with the
   variables that were quantified over. *)
type to_subst = var array * term

(** [matches p t] instantiates the [TRef]'s of [p] so that [p] gets equal
   to [t] and returns [true] if all [TRef]'s of [p] could be instantiated, and
   [false] otherwise. With [allow_binder_holes], a [TRef] belonging to a
   selection pattern may match a term containing a variable bound inside
   [p]. Callers must preserve the scope of those variables when using the
   assignments, or discard them. *)
let matches ?(allow_binder_holes=false) : term -> term -> bool =
  let exception Not_equal in
  let add_eqs xs = List.fold_left2 (fun l pi ti -> (xs,pi,ti)::l) in
  let rec eq l =
    match l with
    | [] -> ()
    | (xs,p,t)::l ->
      if Term.cmp p t = 0 then eq l else begin
      let hp, ps, kp = get_args_len p and ht, ts, kt = get_args_len t in
      if Logger.log_enabled() then
        log "%a %a \nmatches? %a %a"
          term hp (D.list term) ps term ht (D.list term) ts;
      match hp with
      | Wild -> assert false (* used in user syntax only *)
      | Patt _ -> assert false (* used in rules only *)
      | Plac _ -> assert false (* used in scoping only *)
      | Appl _ -> assert false (* not possible after get_args_len *)
      | Type -> assert false (* not possible because of typing *)
      | Kind -> assert false (* not possible because of typing *)
      | Bvar _ -> assert false (* used in reduction only *)
      | TRef r ->
        if kp > kt then raise Not_equal;
        let ts1, ts2 = List.cut ts (kt-kp) in
        let u = add_args ht ts1 in
        (* Ordinary substitutions must be closed under the binders traversed
           by [eq]. Selector holes are allowed to depend on those binders. *)
        if not allow_binder_holes && List.exists (fun x -> occur x u) xs
        then raise Not_equal;
        if Logger.log_enabled() then log (Color.red "<TRef> ≔ %a") term u;
        Timed.(r := Some u);
        eq (add_eqs xs l ps ts2)
      | Meta _ -> eq l (* We assume that metas can always be instantiated by
                          the corresponding RHS although this might not be the
                          case, in which case tac_refine or solve will later
                          fail. This way, we may chose the wrong subterm. *)
      | Prod _
      | Abst _
      | LLet _
      | Symb _
      | Vari _ ->
        if kp <> kt then raise Not_equal;
        match hp, ht with
        | Vari x, Vari y when eq_vars x y -> eq (add_eqs xs l ps ts)
        | Symb f, Symb g when f == g -> eq (add_eqs xs l ps ts)
        | Abst(a,b), Abst(a',b')
        | Prod(a,b), Prod(a',b') ->
            let x,b,b' = unbind2 b b' in
            eq ((xs,a,a')::(x::xs,b,b')::add_eqs xs l ps ts)
        | LLet(a,c,b), LLet(a',c',b') ->
            let x,b,b' = unbind2 b b' in
            eq ((xs,a,a')::(xs,c,c')::(x::xs,b,b')
                ::add_eqs xs l ps ts)
        | _ ->
          if Logger.log_enabled() then log "distinct heads";
          raise Not_equal
      end
  in
  fun p t ->
  let r = try eq [[],p,t]; true with Not_equal -> false in
  if Logger.log_enabled() then log "matches result: %b" r; r

let no_match ?(subterm=false) pos p t =
  if subterm then fatal pos "No subterm of [%a] matches [%a]." term t term p
  else fatal pos "[%a] doesn't match [%a]." term t term p

(** [matching_subs (xs,p) t] attempts to match the pattern [p] containing the
   variables [xs]) with the term [t]. If successful, it returns [Some ts]
   where [ts] is an array of terms such that substituting [xs] by the
   corresponding elements of [ts] in [p] yields [t].

WARNING: Some elements of [ts] may be uninstantiated TRef's. It will happen if
not all [vars] are in [LibTerm.free_vars p], for instance when some [vars] are
type variables not occurring in [p], for instance when trying to apply an
equation of the form [x = ...] with [x] of polymorphic type. This could be
improved by generating p_terms instead of terms. Indeed, in this case, we
could replace uninstantiated TRef's by underscores. *)
let matching_subs : to_subst -> term -> term array option = fun (xs,p) t ->
  (* We replace [xs] by fresh [TRef]'s. *)
  let ts = Array.map (fun _ -> mk_TRef(Timed.ref None)) xs in
  let p = msubst (bind_mvar xs p) ts in
  if matches p t then Some ts else None

(** [check_subs vars ts] check that no element of [ts] is an uninstantiated
    TRef. *)
let check_subs pos vars ts =
  let f i ti =
    match unfold ti with
    | TRef _ ->
        fatal pos "Don't know how to instantiate the argument \"%a\" \
                   of the equation." var vars.(i)
    | _ -> ()
  in
  Array.iteri f ts

let matching_subs_check_TRef pos ((vars,p) as xsp) t =
  match matching_subs xsp t with
  | Some ts -> check_subs pos vars ts; ts
  | None -> no_match pos p t

(** [matching_subs_for_replacement xsp t f] tries to match [xsp] against [t]
    and calls [f] with the produced substitution while the matching references
    are still alive. It restores them before returning. *)
let matching_subs_for_replacement :
    to_subst -> term -> (term array -> 'a option) -> 'a option =
  fun xsp t f ->
  let time = Timed.Time.save () in
  match matching_subs xsp t with
  | None -> Timed.Time.restore time; None
  | Some subst ->
      let result = f subst in
      Timed.Time.restore time;
      result

(** Binder frame enclosing a subterm found by [find_subst]. *)
type binder_frame =
  { binder_var : var
  ; binder_typ : term
  ; binder_path : int list }

(** [abstract_over_frame frame t] abstracts [t] over the variable recorded in
    [frame], using the frame's binder type. *)
let abstract_over_frame : binder_frame -> term -> term =
  fun frame t ->
  mk_Abst(frame.binder_typ, bind_var frame.binder_var t)

(** [abstract_over_frames frames t] abstracts [t] over all [frames]. The frame
    list must be ordered from innermost to outermost binder, and the returned
    abstractions are nested from outermost to innermost binder. *)
let abstract_over_frames : binder_frame list -> term -> term =
  fun frames t ->
  List.fold_left
    (fun t frame -> abstract_over_frame frame t)
    t frames

(** [same_binder_paths frames frames'] tells whether [frames] and [frames']
    identify the same original enclosing binders across independent
    traversals of the goal. *)
let same_binder_paths : binder_frame list -> binder_frame list -> bool =
  List.equal (fun f f' -> f.binder_path = f'.binder_path)

(** [find_subterm_from binders path try_match t] searches [t], trying each
    candidate before its children. [try_match] receives its enclosing frames
    and term, and returns [Some result] on success. Failed attempts are
    rolled back before descending. Children are searched in application order,
    with binder domains and let definitions before bodies. Initial frames are
    ordered from innermost to outermost; paths store child indices in reverse.
    A successful result retains the state established by [try_match]. *)
let find_subterm_from :
    binder_frame list -> int list ->
    (binder_frame list -> term -> 'a option) ->
    term -> 'a option =
  fun initial_binders initial_path try_match t ->
  let time = Timed.Time.save () in
  let rec find binders path t =
    match try_match binders t with
    | Some _ as r -> r
    | None ->
        Timed.Time.restore time;
        match unfold t with
        | Appl(a,b) -> find2 binders path a b
        | Abst(a,b) | Prod(a,b) -> find_binder binders path a b
        | LLet(a,c,b) -> find3 binders path a c b
        | _ -> None
  and find2 binders path a b =
    match find binders (0::path) a with
    | None -> Timed.Time.restore time; find binders (1::path) b
    | r -> r
  and find3 binders path a c b =
    match find binders (0::path) a with
    | Some _ as r -> r
    | None ->
        Timed.Time.restore time;
        match find binders (1::path) c with
        | None ->
            Timed.Time.restore time;
            let x,b = unbind b in
            let frame =
              { binder_var = x; binder_typ = a; binder_path = 2::path }
            in
            find (frame::binders) (2::path) b
        | r -> r
  and find_binder binders path a b =
    match find binders (0::path) a with
    | None ->
        Timed.Time.restore time;
        let x,b = unbind b in
        let frame =
          { binder_var = x; binder_typ = a; binder_path = 1::path }
        in
        find (frame::binders) (1::path) b
    | r -> r
  in find initial_binders initial_path t

(** Result of a successful binder-aware rewrite occurrence search. *)
type subst_under_binders =
  { subst : term array
  ; redex : term
  ; binders : binder_frame list }

(** [find_subst_from binders path (xs,p) t] searches for the first subterm of
    [t] matching [p]. It returns the substitution for [xs], the matched term
    and its enclosing binder frames. [binders] and [path] are the known
    enclosing context of [t], ordered as in [find_subterm_from]. *)
let find_subst_from :
    binder_frame list -> int list -> to_subst -> term ->
    subst_under_binders option = fun initial_binders initial_path xsp t ->
  let try_match binders t =
    if Logger.log_enabled() then
      log "find_subst %a ≡ %a" term (snd xsp) term t;
    match matching_subs xsp t with
    | None -> None
    | Some subst -> Some { subst; redex = t; binders }
  in
  find_subterm_from initial_binders initial_path try_match t

(** [find_subst (xs,p) t] calls
[find_subst_from binders path (xs,p) t] with an empty
initial binder context and path. *)
let find_subst :
    to_subst -> term -> subst_under_binders option =
  find_subst_from [] []

(** [find_subst pos (vars,p) t] returns the first occurrence
    search result for [p] in [t], or fails if no subterm matches. It also
    checks that all variables in [vars] have been instantiated. *)
let find_subst :
    popt -> to_subst -> term -> subst_under_binders = fun pos (vars,p) t ->
  match find_subst (vars,p) t with
  | None -> no_match ~subterm:true pos p t
  | Some r -> check_subs pos vars r.subst; r

(** [find_subst_in_region pos binders (vars,p) t] searches for
    [p] in an already-selected region [t], preserving the binder context
    enclosing the region. *)
let find_subst_in_region :
    popt -> binder_frame list -> to_subst -> term -> subst_under_binders =
  fun pos binders (vars,p) t ->
  match find_subst_from binders [] (vars,p) t with
  | None -> no_match ~subterm:true pos p t
  | Some r -> check_subs pos vars r.subst; r

(** [replace_wild_by_tref t] substitutes every wildcard of [t] by a distinct
   fresh [TRef]. *)
let rec replace_wild_by_tref : term -> term = fun t ->
  match unfold t with
  | Wild -> mk_TRef(Timed.ref None)
  | Appl(t,u) ->
    mk_Appl_not_canonical(replace_wild_by_tref t, replace_wild_by_tref u)
  | Abst(a,b) ->
    let x,b = unbind b in
    mk_Abst(replace_wild_by_tref a,
            bind_var x (replace_wild_by_tref b))
  | Prod(a,b) ->
    let x,b = unbind b in
    mk_Prod(replace_wild_by_tref a,
            bind_var x (replace_wild_by_tref b))
  | LLet(a,c,b) ->
    let x,b = unbind b in
    mk_LLet(replace_wild_by_tref a, replace_wild_by_tref c,
            bind_var x (replace_wild_by_tref b))
  | _ -> t

(** Term selected by a rewrite selector pattern, together with the binders
    enclosing the selected occurrence. *)
type selected_term_under_binders =
  { selected : term
  ; selected_binders : binder_frame list }

(** [find_subterm_matching_from binders path p t] tries to find
    a subterm of [t] that matches [p] by instantiating the [TRef]'s of [p]
    and records the binders enclosing the selected subterm. [binders] and
    [path] are the already-known enclosing binder context of [t]. The binder
    list is ordered from innermost to outermost binder. *)
let find_subterm_matching_from :
    binder_frame list -> int list -> term -> term ->
    selected_term_under_binders option =
  fun initial_binders initial_path p t ->
  let p_refs = replace_wild_by_tref p in
  let try_match binders t =
    (* Keep the actual goal subterm: a wildcard instantiated with a bound
       variable in [p_refs] is meaningful only while that binder is open. *)
    if matches ~allow_binder_holes:true p_refs t then Some
        { selected = t; selected_binders = binders }
    else None
  in
  find_subterm_from initial_binders initial_path try_match t

(** [find_subterm_matching p t] is
    [find_subterm_matching_from] with no initial enclosing
    binders. *)
let find_subterm_matching :
    term -> term -> selected_term_under_binders option =
  find_subterm_matching_from [] []

(** [find_subterm_matching pos p t] returns the first selected
    subterm matching [p] in [t], or fails if no subterm matches. *)
let find_subterm_matching :
    popt -> term -> term -> selected_term_under_binders = fun pos p t ->
  match find_subterm_matching p t with
  | None -> no_match ~subterm:true pos p t
  | Some r -> r

(** Result of matching a contextual pattern such as [id in p]. [context] is
    the first subterm of the goal matching [p]; [selected_context] is the
    subterm denoted by [id] inside it. A selector can denote [f x] where [x]
    is bound by [p], so both terms retain their enclosing binder frames.
    [selected_path] is the first occurrence of [id], and [selected_paths]
    records every occurrence. These paths are relative to [context] and are
    stored in reverse order, as in the rewrite traversal. *)
type contextual_selection =
  { context : term
  ; context_binders : binder_frame list
  ; selected_context : term
  ; selected_context_binders : binder_frame list
  ; selected_path : int list
  ; selected_paths : int list list }

(** [match_contextual_pattern ~accept selector p binders t] matches one
    candidate [t] against [p], collecting all occurrences of [selector]. The
    selected paths are relative to [t]; [binders] records its enclosing
    context. [accept] optionally constrains the selected term. *)
let match_contextual_pattern :
    ?accept:(term -> bool) -> var -> term -> binder_frame list -> term ->
    contextual_selection option =
  fun ?(accept=fun _ -> true) selector p binders t ->
  (* Repeated occurrences of the selector must denote the same term under
     the same original binders. Abstracting both terms over their frames
     makes freshly unbound variable names irrelevant to this comparison. *)
  let same fs fs' u t =
    same_binder_paths fs fs'
    && Term.cmp
         (abstract_over_frames fs u) (abstract_over_frames fs' t) = 0
  in
  let selected = ref None in
  (* Match one candidate [t] against the whole context pattern. The first
     selector occurrence records its term and path; later occurrences must
     agree and add their own paths. Wildcards impose no such equality. *)
  let rec match_pattern binders path p t =
    match unfold p, unfold t with
    | Vari x, _ when eq_vars x selector ->
        begin match !selected with
        | None -> selected := Some(t,binders,[path]); true
        | Some(u,fs,paths) ->
            if same fs binders u t then
              (selected := Some(u,fs,path::paths); true)
            else false
        end
    | Wild, _ -> true
    | Vari x, Vari y -> eq_vars x y
    | Symb f, Symb g -> f == g
    | Type, Type | Kind, Kind -> true
    | Appl(p,q), Appl(t,u) ->
        match_pattern binders (0::path) p t
        && match_pattern binders (1::path) q u
    | Abst(a,b), Abst(a',b')
    | Prod(a,b), Prod(a',b') ->
        (* Use one fresh variable for both bodies. *)
        let x,b,b' = unbind2 b b' in
        match_pattern binders (0::path) a a'
        && let frame =
             { binder_var = x; binder_typ = a'; binder_path = 1::path }
           in
           match_pattern (frame::binders) (1::path) b b'
    | LLet(a,c,b), LLet(a',c',b') ->
        let x,b,b' = unbind2 b b' in
        match_pattern binders (0::path) a a'
        && match_pattern binders (1::path) c c'
        && let frame =
             { binder_var = x; binder_typ = a'; binder_path = 2::path }
           in
           match_pattern (frame::binders) (2::path) b b'
    | _ -> false
  in
  (* Paths collected during matching start at this candidate context.
     [accept] is tested before searching beneath a rejected candidate;
     this matters when an explicit [as] pattern skips an earlier context. *)
  if match_pattern binders [] p t then
    match !selected with
    | Some(u,fs,selected_paths) when accept u ->
        let selected_path = List.hd (List.rev selected_paths) in
        Some { context = t; context_binders = binders
             ; selected_context = u; selected_context_binders = fs
             ; selected_path; selected_paths }
    | _ -> None
  else None

(** [find_contextual_selection ~accept pos p goal] finds the first subterm of
    [goal] matching the contextual pattern [p]. It matches the context and
    identifies the selector occurrence together, [accept] optionally 
    constrains the selected term, as required by [term as id in context]. *)
let find_contextual_selection :
    ?accept:(term -> bool) -> popt -> binder -> term ->
    contextual_selection = fun ?(accept=fun _ -> true) pos p goal ->
  let selector,p = unbind p in
  let match_context = match_contextual_pattern ~accept selector p in
  match find_subterm_from [] [] match_context goal with
  | Some r -> r
  | None -> no_match ~subterm:true pos p goal

(** [bind_pattern p t] replaces in the term [t] every occurence of the pattern
   [p] by a fresh variable, and returns the binder on this variable. *)
let bind_pattern : term -> term -> binder =  fun p t ->
  let z = new_var "z" in
  let rec replace : term -> term = fun t ->
    if matches p t then mk_Vari z else
    match unfold t with
    | Appl(t,u) -> mk_Appl (replace t, replace u)
    | Prod(a,b) ->
        let x,b = unbind b in
        mk_Prod (replace a, bind_var x (replace b))
    | Abst(a,b) ->
        let x,b = unbind b in
        mk_Abst (replace a, bind_var x (replace b))
    | LLet(typ, def, body) ->
        let x, body = unbind body in
        mk_LLet (replace typ, replace def, bind_var x (replace body))
    | Meta(m,ts) -> mk_Meta (m, Array.map replace ts)
    | Bvar _ -> assert false
    | Wild -> assert false
    | TRef _ -> assert false
    | Patt _ -> assert false
    | Plac _ -> assert false
    | _ -> t
  in
  bind_var z (replace t)

(** [apply_to_frames t frames] applies [t] to the variables in [frames]. The
    frame list must be ordered from innermost to outermost binder. *)
let apply_to_frames : term -> binder_frame list -> term =
  fun t frames ->
  List.fold_right
    (fun frame t -> mk_Appl(t, mk_Vari frame.binder_var))
    frames t

(** [adapt_to_frames frames frames' t] if [t] contains the variables bound
    by [frames], [t] is adapted so that it refers to the corresponding
    variables bound by [frames']. *)
let adapt_to_frames :
    binder_frame list -> binder_frame list -> term -> term =
  fun frames frames' t ->
  apply_to_frames (abstract_over_frames frames t) frames'

(** [same_under_binders first_frames frames first t] tells whether [t] is the
    same term as [first], modulo the fresh variables generated when unbinding
    the same original enclosing binders. *)
let same_under_binders :
    binder_frame list -> binder_frame list -> term -> term -> bool =
  fun first_frames frames first t ->
  same_binder_paths first_frames frames
  && LibTerm.eq_alpha
       (abstract_over_frames first_frames first)
       (abstract_over_frames frames t)

(** [same_substitution_under_binders first_subst first_frames frames subst]
    tells whether [subst], found under [frames], belongs to the occurrence
    class determined by [first_subst]. Occurrence arguments are compared
    with [same_under_binders], so selected occurrences must refer to the
    same original binders as the first occurrence. *)
let same_substitution_under_binders :
    term array -> binder_frame list -> binder_frame list -> term array ->
    bool =
  fun first_subst first_frames frames subst ->
  Array.length first_subst = Array.length subst
  && Array.for_all2 (same_under_binders first_frames frames)
    first_subst subst

(** [replace_under_binders_from binders path f goal] traverses [goal] while
    recording enclosing binder frames. [binders] and [path] are the
    already-known enclosing binder context of [goal]. At each subterm [t],
    [f binders path t] may return a replacement. The path is relative to the
    initial [goal] unless [path] is supplied by a containing search. If [f]
    returns a replacement, traversal does not descend below [t]. *)
let replace_under_binders_from :
    binder_frame list -> int list ->
    (binder_frame list -> int list -> term -> term option) -> term -> term =
  fun initial_binders initial_path f goal ->
  let rec replace : binder_frame list -> int list -> term -> term =
    fun binders path t ->
    match f binders path t with
    | Some t -> t
    | None ->
        match unfold t with
        | Appl(t,u) ->
            mk_Appl (replace binders (0::path) t,
                     replace binders (1::path) u)
        | Prod(a,b) ->
            let x,b = unbind b in
            let frame =
              { binder_var = x; binder_typ = a; binder_path = 1::path }
            in
            mk_Prod (replace binders (0::path) a,
                     bind_var x (replace (frame::binders) (1::path) b))
        | Abst(a,b) ->
            let x,b = unbind b in
            let frame =
              { binder_var = x; binder_typ = a; binder_path = 1::path }
            in
            mk_Abst (replace binders (0::path) a,
                     bind_var x (replace (frame::binders) (1::path) b))
        | LLet(typ, def, body) ->
            let x, body = unbind body in
            let frame =
              { binder_var = x; binder_typ = typ; binder_path = 2::path }
            in
            mk_LLet (replace binders (0::path) typ,
                     replace binders (1::path) def,
                     bind_var x
                       (replace (frame::binders) (2::path) body))
        | Meta(m,ts) -> mk_Meta (m, Array.map (replace binders path) ts)
        | Bvar _ -> assert false
        | Wild -> assert false
        | TRef _ -> assert false
        | Patt _ -> assert false
        | Plac _ -> assert false
        | _ -> t
  in
  replace initial_binders initial_path goal

(** [replace_under_binders f goal] traverses [goal] while recording enclosing
    binder frames. At each subterm [t], [f binders t] may return a
    replacement. If it does, traversal does not descend below [t]. *)
let replace_under_binders :
    (binder_frame list -> term -> term option) -> term -> term =
  fun f -> replace_under_binders_from [] [] (fun fs _ t -> f fs t)

(** [bind_pattern_under_binders_from ~at binders z xsp first_subst relevant
    goal] is the binder-aware counterpart of [bind_pattern]. [binders] is the
    already-known enclosing binder context of [goal]. It replaces occurrences
    matching the first occurrence's shape by [z] applied to the corresponding
    local binder variables. [at] additionally restricts replacement to paths
    selected by a contextual pattern; without it, every matching occurrence
    is considered. *)
let bind_pattern_under_binders_from ?(at=fun _ -> true) :
    binder_frame list -> var -> to_subst -> term array -> binder_frame list ->
    term -> term = fun initial_binders z xsp first_subst relevant goal ->
  let replace binders path t =
    let current_relevant =
      List.filter (fun frame -> occur frame.binder_var t) binders in
    (* A path alone is insufficient: the occurrence must also depend on the
       same binders and instantiate the lemma like the first redex. *)
    if at path && List.length current_relevant = List.length relevant then
      matching_subs_for_replacement xsp t (fun subst ->
        if same_substitution_under_binders
             first_subst relevant current_relevant subst
        then Some (apply_to_frames (mk_Vari z) current_relevant)
        else None)
    else None
  in
  replace_under_binders_from initial_binders [] replace goal

(** [replace_selected_under_binders selected_binders selected replacement
    goal]
    replaces every occurrence of [selected] in [goal] by [replacement],
    adapting references to enclosing binder variables when the same original
    binder is unbound again while traversing [goal]. *)
let replace_selected_under_binders :
    binder_frame list -> term -> term -> term -> term =
  fun selected_binders selected replacement goal ->
  let selected_binders =
    List.filter (fun frame -> occur frame.binder_var selected)
      selected_binders
  in
  let replace binders t =
    let current_binders =
      List.filter (fun frame -> occur frame.binder_var t) binders
    in
    if same_under_binders selected_binders current_binders selected t then
      Some (adapt_to_frames selected_binders current_binders replacement)
    else None
  in
  replace_under_binders replace goal

(** Data prepared for the final equality-induction rewrite step. *)
type prepared_rewrite =
  { eq_type : term
  ; lhs : term
  ; rhs : term
  ; proof : term
  ; pred_bind : binder
  ; new_term : term }

(** Equality data being lifted over one or more binders. *)
type eq_data = term * term * term * term

(** [hol_domain_of_binder cfg pos typ] returns [a] when [typ] is convertible
    to [T a], and fails otherwise. *)
let hol_domain_of_binder : eq_config -> popt -> term -> term =
  fun cfg pos typ ->
  (* User rewrite rules must not be used here:
    a type such as [T o] may reduce to the underlying host type [Prop]. *)
  match get_args (Eval.whnf ~tags:[NoRw] [] typ) with
  | t, [a] when is_symb cfg.symb_T t -> a
  | _ -> fatal pos
           "Expected a non-dependent HOL binder type of the form %a _."
           sym cfg.symb_T

(** [lift_over_frame cfg binder_cfg pos frame (a,l,r,p)] lifts the equality
    data [p : P (eq a l r)] over [frame] using [funExt]. *)
let lift_over_frame : eq_config -> binder_rewrite_config -> popt ->
    binder_frame -> eq_data -> eq_data =
  fun cfg binder_cfg pos frame (eq_type, lhs, rhs, proof) ->
  let dom = hol_domain_of_binder cfg pos frame.binder_typ in
  let cod = eq_type in
  let eq_type = add_args (mk_Symb binder_cfg.symb_arr) [dom; cod] in
  let lhs = abstract_over_frame frame lhs in
  let rhs = abstract_over_frame frame rhs in
  let proof = abstract_over_frame frame proof in
  let proof =
    add_args (mk_Symb binder_cfg.symb_funext) [dom; cod; lhs; rhs; proof]
  in
  eq_type, lhs, rhs, proof

(** [prepare_eq_data_under_binders ss cfg pos binders redex data] lifts
    [data] over every enclosing binder on which [redex] depends. It returns
    the lifted equality data and the relevant binders. *)
let prepare_eq_data_under_binders :
    Sig_state.t -> eq_config -> popt -> binder_frame list -> term ->
    eq_data -> eq_data * binder_frame list =
  fun ss cfg pos binders redex (eq_type, lhs, rhs, proof) ->
  let relevant =
    List.filter (fun frame -> occur frame.binder_var redex) binders
  in
  match relevant with
  | [] -> (eq_type, lhs, rhs, proof), relevant
  | _ ->
      let binder_cfg = get_binder_rewrite_config ss pos in
      let data =
        List.fold_left
          (fun acc frame -> lift_over_frame cfg binder_cfg pos frame acc)
          (eq_type, lhs, rhs, proof) relevant
      in
      data, relevant

(** [prepare_rewrite_under_binders_from binders ss cfg pos xsp goal eq_data
    found] prepares the equality data and rewrite context for an ordinary
    rewrite occurrence. [binders] is the already-known enclosing binder
    context of [goal]. If the redex is independent from its enclosing binders,
    the old direct rewrite data is returned. Otherwise, the equality is lifted
    over the relevant binders and the context abstracts the resulting
    function-level occurrence. *)
let prepare_rewrite_under_binders_from :
    binder_frame list -> Sig_state.t -> eq_config -> popt -> to_subst ->
    term -> eq_data -> subst_under_binders -> prepared_rewrite =
  fun initial_binders ss cfg pos xsp goal (eq_type, lhs, rhs, proof) found ->
  let (eq_type, lhs, rhs, proof), relevant =
    prepare_eq_data_under_binders ss cfg pos found.binders found.redex
      (eq_type, lhs, rhs, proof)
  in
  match relevant with
  | [] ->
      let pred_bind = bind_pattern lhs goal in
      { eq_type; lhs; rhs; proof; pred_bind; new_term = subst pred_bind rhs }
  | _ ->
      let z = new_var "z" in
      let pred =
        bind_pattern_under_binders_from
          initial_binders z xsp found.subst relevant goal
      in
      let pred_bind = bind_var z pred in
      { eq_type; lhs; rhs; proof; pred_bind; new_term = subst pred_bind rhs }

(** [prepare_rewrite_under_binders ss cfg pos xsp goal eq_data found] is
    [prepare_rewrite_under_binders_from] with no initial enclosing binders. *)
let prepare_rewrite_under_binders :
    Sig_state.t -> eq_config -> popt -> to_subst -> term -> eq_data ->
    subst_under_binders -> prepared_rewrite =
  prepare_rewrite_under_binders_from []

(** [prepare_rewrite_in_context at binders ss cfg pos xsp goal data found]
    builds the equality proof, predicate and new term inside one matched
    contextual region. [at] decides which paths of that region may be
    replaced. It is applied even if the redex is independent of its enclosing
    binders; otherwise an identical redex elsewhere in the context could be
    rewritten despite not being selected by [id in context]. *)
let prepare_rewrite_in_context :
    (int list -> bool) -> binder_frame list -> Sig_state.t -> eq_config ->
    popt -> to_subst -> term -> eq_data -> subst_under_binders ->
    prepared_rewrite =
  fun at initial_binders ss cfg pos xsp goal data found ->
  let (eq_type, lhs, rhs, proof), relevant =
    prepare_eq_data_under_binders ss cfg pos found.binders found.redex data
  in
  (* The predicate contains [z] at the chosen occurrences. When [found]
     depends on local binders, those occurrences use [z] applied to their
     corresponding bound variables, matching the lifted equality proof. *)
  let z = new_var "z" in
  let pred =
    bind_pattern_under_binders_from ~at
      initial_binders z xsp found.subst relevant goal
  in
  let pred_bind = bind_var z pred in
  { eq_type; lhs; rhs; proof; pred_bind; new_term = subst pred_bind rhs }

(** [swap cfg a r l t] returns a term of type [P (eq a l r)] from a term [t]
   of type [P (eq a r l)]. *)
let swap : eq_config -> term -> term -> term -> term -> term =
  fun cfg a r l t ->
  (* We build the predicate “λx:T a, eq a l x”. *)
  let pred =
    let x = new_var "x" in
    let pred = add_args (mk_Symb cfg.symb_eq) [a; l; mk_Vari x] in
    mk_Abst(mk_Appl(mk_Symb cfg.symb_T, a), bind_var x pred)
  in
  (* We build the proof term. *)
  let refl_a_l = add_args (mk_Symb cfg.symb_refl) [a; l] in
  add_args (mk_Symb cfg.symb_eqind) [a; r; l; t; pred; refl_a_l]

(** [rewrite ss p pos gt l2r pat t] generates a term for the refine tactic
   representing the application of the rewrite tactic to the goal type
   [gt]. Every occurrence of the first instance of the left-hand side is
   replaced by the right-hand side of the obtained proof (or the reverse if
   l2r is false). [pat] is an optional SSReflect pattern. [t] is the
   equational lemma that is appied. It handles the full set of SSReflect
   patterns. *)
let rewrite : Sig_state.t -> problem -> popt -> goal_typ -> bool ->
              (term, binder) Parsing.Syntax.rwpatt option -> term -> term =
  fun ss p pos {goal_hyps=g_env; goal_type=g_type; _} l2r pat t ->

  (* Obtain the required symbols from the current signature. *)
  let cfg = get_eq_config ss pos in

  (* Extract the term from the goal type (get “u” from “P u”). *)
  let g_term =
    match get_args g_type with
    | t, [u] when is_symb cfg.symb_P t -> u
    | _ -> fatal pos "Goal not of the form (%a _)." sym cfg.symb_P
  in

  (* Infer the type of [t] (the argument given to the tactic). *)
  let g_ctxt = Env.to_ctxt g_env in
  let (t, t_type) = Query.infer pos p g_ctxt t in

  (* Check that [t_type ≡ Π x1:a1, ..., Π xn:an, P (eq a l r)]. *)
  let (a, l, r), vars = get_eq_data cfg pos t_type in
  let vars = Array.of_list vars in

  (* Apply [t] to the variables of [vars] to get a witness of the equality. *)
  let t = Array.fold_left (fun t x -> mk_Appl(t, mk_Vari x)) t vars in

  (* Reverse the members of the equation if l2r is false. *)
  let (t, l, r) = if l2r then (t, l, r) else (swap cfg a l r t, r, l) in

  (* Bind the variables in this new witness. *)
  let bound = let bind = bind_mvar vars in bind t, bind l, bind r in
  let msubst3 (b1, b2, b3) ts = msubst b1 ts, msubst b2 ts, msubst b3 ts in

  (* An [id in context] or [term as id in context] pattern rewrites exactly
     the occurrences named by [id]. [selected_paths] includes repeated uses
     of that identifier in the matched context. *)
  let at_selector selected path = List.mem path selected.selected_paths in

  (* The forms [in id in context] and [term in id in context] search for a
     redex inside the region named by [id]. Paths grow by prepending child
     indices, so a descendant path ends with its region's path. *)
  let within_selector selected path =
    let rec drop n xs =
      if n = 0 then xs else match xs with
      | [] -> []
      | _::xs -> drop (n-1) xs
    in
    List.exists (fun root ->
      let delta = List.length path - List.length root in
      delta >= 0 && drop delta path = root)
      selected.selected_paths
  in

  (* Finish a contextual rewrite after its first redex and lemma substitution
     have been found. First rewrite inside the matched context, retaining its
     enclosing binders. Then plug the rewritten context and the corresponding
     equality-induction predicate back into the complete goal. Keeping
     [lhs_pattern] separate from the instantiated [l] is necessary when
     comparing later occurrences with the first lemma substitution. *)
  let rewrite_in_context at selected found =
    let lhs_pattern = l in
    let (t,l,r) = msubst3 bound found.subst in
    let prepared =
      prepare_rewrite_in_context at
        selected.context_binders ss cfg pos (vars,lhs_pattern)
        selected.context (a,l,r,t) found
    in
    (* [prepared.pred_bind] binds the equality-induction variable in the
       context. Reuse that variable when placing the predicate in [g_term]. *)
    let z,region_pred = unbind prepared.pred_bind in
    let new_term =
      replace_selected_under_binders selected.context_binders
        selected.context prepared.new_term g_term
    in
    let pred =
      replace_selected_under_binders selected.context_binders
        selected.context region_pred g_term
    in
    ( prepared.eq_type, bind_var z pred, new_term
    , prepared.proof, prepared.lhs, prepared.rhs )
  in

  (* Obtain the different components depending on the pattern. *)
  let (a, pred_bind, new_term, t, l, r) =
    match pat with
    (* Simple rewrite, no pattern. *)
    | None ->
        (* Build a substitution from the first instance of [l] in the goal. *)
        let lhs_pattern = l in
        let found = find_subst pos (vars, l) g_term in
        (* Build the required data from that substitution. *)
        let (t, l, r) = msubst3 bound found.subst in
        let prepared = prepare_rewrite_under_binders
            ss cfg pos (vars, lhs_pattern) g_term (a, l, r, t) found
        in
        ( prepared.eq_type, prepared.pred_bind, prepared.new_term
        , prepared.proof, prepared.lhs, prepared.rhs )

    (* Basic patterns. *)
    | Some(Rw_Term(p)) ->
        (* Find a subterm [match_p] of the goal that matches [p]. *)
        let match_p = find_subterm_matching pos p g_term in
        let lhs_pattern = l in
        (* Build a substitution by matching [match_p] with the LHS [l]. *)
        let sigma = matching_subs_check_TRef pos (vars,l) match_p.selected in
        (* Build the data from the substitution. *)
        let (t, l, r) = msubst3 bound sigma in
        let found =
          { subst = sigma; redex = match_p.selected
          ; binders = match_p.selected_binders }
        in
        let prepared = prepare_rewrite_under_binders
            ss cfg pos (vars, lhs_pattern) g_term (a, l, r, t) found
        in
        ( prepared.eq_type, prepared.pred_bind, prepared.new_term
        , prepared.proof, prepared.lhs, prepared.rhs )

    (* Nested patterns. *)
    | Some(Rw_InTerm(p)) ->
        (* Find the selected region, then search for the rewrite redex inside
           it without dropping the binders enclosing the region. *)
        let selected = find_subterm_matching pos p g_term in
        let lhs_pattern = l in
        let found =
          find_subst_in_region
            pos selected.selected_binders (vars,l) selected.selected
        in
        let (t, l, r) = msubst3 bound found.subst in
        let prepared =
          prepare_rewrite_under_binders_from
            selected.selected_binders ss cfg pos (vars, lhs_pattern)
            selected.selected (a, l, r, t) found
        in
        let region_var, region_pred = unbind prepared.pred_bind in
        let new_term =
          replace_selected_under_binders
            selected.selected_binders selected.selected
            prepared.new_term g_term
        in
        let pred =
          replace_selected_under_binders
            selected.selected_binders selected.selected
            region_pred g_term
        in
        ( prepared.eq_type, bind_var region_var pred, new_term
        , prepared.proof, prepared.lhs, prepared.rhs )

    | Some(Rw_IdInTerm(p)) ->
        (* [id in context]: find the first matching context and take the term
           denoted by [id] itself as the redex. It may contain variables
           bound inside [context], so retain its frames for proof lifting. *)
        let selected = find_contextual_selection pos p g_term in
        let redex = selected.selected_context in
        let sigma = matching_subs_check_TRef pos (vars,l) redex in
        let found =
          { subst = sigma; redex
          ; binders = selected.selected_context_binders }
        in
        (* Only the positions occupied by [id] are rewritten, even if an
           identical term appears elsewhere in the context. *)
        rewrite_in_context (at_selector selected) selected found

    (* Combinational patterns. *)
    | Some(Rw_TermInIdInTerm(s,p)) ->
        (* [term in id in context]: first select the region named by [id],
           then find an instance of the explicit redex pattern [s] inside it.
           Start with the selector's binder frames and path, so the resulting
           redex path is relative to the matched context as a whole. *)
        let selected = find_contextual_selection pos p g_term in
        let found_s =
          match find_subterm_matching_from
                  selected.selected_context_binders selected.selected_path
                  s selected.selected_context with
          | Some r -> r
          | None -> no_match ~subterm:true pos s selected.selected_context
        in
        let sigma = matching_subs_check_TRef pos (vars,l) found_s.selected in
        let found =
          { subst = sigma; redex = found_s.selected
          ; binders = found_s.selected_binders }
        in
        (* The explicit pattern fixes the first lemma instance; matching
           occurrences in the selected region receive the same rewrite. *)
        rewrite_in_context (within_selector selected) selected found

    | Some(Rw_TermAsIdInTerm(s,p)) ->
        (* [term as id in context] constrains [id] to match [s] while finding
           the context. Test that constraint for each candidate, rather than
           accepting an earlier context whose [id] has the wrong shape. *)
        let accept redex =
          let time = Timed.Time.save () in
          let result =
            matches ~allow_binder_holes:true
              (replace_wild_by_tref s) redex
          in
          (* A failed candidate must not leave wildcard instantiations for
             the next candidate examined by the context search. *)
          Timed.Time.restore time;
          result
        in
        let selected = find_contextual_selection ~accept pos p g_term in
        let redex = selected.selected_context in
        let sigma = matching_subs_check_TRef pos (vars,l) redex in
        let found =
          { subst = sigma; redex
          ; binders = selected.selected_context_binders }
        in
        (* As with [id in context], [id] names the redex positions exactly. *)
        rewrite_in_context (at_selector selected) selected found

    | Some(Rw_InIdInTerm(q)) ->
        (* [in id in context] infers the redex from the lemma and searches
           inside the selected region. Carry the region's binder frames and
           path into that search, including binders introduced by
           [context]. *)
        let selected = find_contextual_selection pos q g_term in
        let found =
          match find_subst_from
                  selected.selected_context_binders selected.selected_path
                  (vars,l) selected.selected_context with
          | Some r -> check_subs pos vars r.subst; r
          | None -> no_match ~subterm:true pos l selected.selected_context
        in
        (* Rewriting is limited to descendants of [id], not other matching
           lemma occurrences in the surrounding context. *)
        rewrite_in_context (within_selector selected) selected found
  in

  (* Construct the predicate (context). *)
  let pred = mk_Abst(mk_Appl(mk_Symb cfg.symb_T, a), pred_bind) in

  (* Construct the new goal and its type. *)
  let goal_type = mk_Appl(mk_Symb cfg.symb_P, new_term) in
  let goal_term = LibMeta.make p g_ctxt goal_type in

  (* Build the final term produced by the tactic. *)
  let eqind = mk_Symb cfg.symb_eqind in
  let result = add_args eqind [a; l; r; t; pred; goal_term] in

  (* Debugging data to the log. *)
  if Logger.log_enabled () then
    begin
      log "Rewriting with:";
      log "  goal           = [%a]" term g_type;
      log "  equality proof = [%a]" term t;
      log "  equality LHS   = [%a]" term l;
      log "  equality RHS   = [%a]" term r;
      log "  pred           = [%a]" term pred;
      log "  new goal       = [%a]" term goal_type;
      log "  produced term  = [%a]" term result;
    end;

  (* Return the proof-term. *)
  result
