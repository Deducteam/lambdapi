(** Evaluation and conversion. *)

open Extra
open Timed
open Console
open Terms
open Print

(** Logging function for evaluation. *)
let log_eval = new_logger 'r' "eval" "debugging information for evaluation"
let log_eval = log_eval.logger

(** Logging function for equality modulo rewriting. *)
let log_eqmd = new_logger 'e' "eqmd" "debugging information for equality"
let log_eqmd = log_eqmd.logger

(** Representation of a stack for the abstract machine used for evaluation. *)
type stack = (bool * term) Pervasives.ref list

(** Representation of a single stack element. *)
type stack_elt = (bool * term) Pervasives.ref

(* NOTE the stack contain references so that the computation of arguments when
   matching reduction rules may be shared. *)

(*******************************)
let rec print_int_list : int list -> unit = function
  | [] -> ()
  | x :: xs -> Printf.printf " | %d" x ; print_int_list xs

(** [to_term t stk] builds a term from an abstract machine state [(t,stk)]. *)
let to_term : term -> stack -> term = fun t args ->
  let rec to_term t args =
    match args with
    | []      -> t
    | u::args -> to_term (Appl(t,snd Pervasives.(!u))) args
  in to_term t args

(** Evaluation step counter. *)
let steps : int Pervasives.ref = Pervasives.ref 0

(** [whnf t] computes a weak head normal form of the term [t]. *)
let rec whnf : term -> term = fun t ->
  if !log_enabled then log_eval "evaluating [%a]" pp t;
  let s = Pervasives.(!steps) in
  let t = unfold t in
  let (u, stk) = whnf_stk t [] in
  if Pervasives.(!steps) <> s then to_term u stk else t

(** [whnf_stk t stk] computes the weak head normal form of  [t] applied to the
    argument list (or stack) [stk]. Note that the normalisation is done in the
    sense of [whnf]. *)
and whnf_stk : term -> stack -> term * stack = fun t stk ->
  let st = (unfold t, stk) in
  match st with
  (* Push argument to the stack. *)
  | (Appl(f,u), stk    ) ->
      whnf_stk f (Pervasives.ref (false, u) :: stk)
  (* Beta reduction. *)
  | (Abst(_,f), u::stk ) ->
      Pervasives.incr steps;
      whnf_stk (Bindlib.subst f (snd Pervasives.(!u))) stk
  (* Try to rewrite. *)
  | (Symb(s,_), stk    ) ->
      begin
        match Timed.(!(s.sym_def)) with
        | Some(t) -> Pervasives.incr steps; whnf_stk t stk
        | None    ->
        match find_rule s stk with
        | None        -> st
        | Some(t,stk) -> Pervasives.incr steps; whnf_stk t stk
      end
  (* In head normal form. *)
  | (_        , _      ) -> st

(** [find_rule s stk] attempts to find a reduction rule of [s], that may apply
    under the stack [stk]. If such a rule is found, the machine state produced
    by its application is returned. *)
and find_rule : sym -> stack -> (term * stack) option = fun s stk ->
  let stk_len = List.length stk in
  let match_rule r =
    (* First check that we have enough arguments. *)
    if r.arity > stk_len then None else
    (* Substitute the left-hand side of [r] with pattern variables *)
    let env = Array.make (Bindlib.mbinder_arity r.rhs) TE_None in
    (* Match each argument of the lhs with the terms in the stack. *)
    let rec match_args ps ts =
      match (ps, ts) with
      | ([]   , _    ) -> Some(Bindlib.msubst r.rhs env, ts)
      | (p::ps, t::ts) -> if matching env p t then match_args ps ts else None
      | (_    , _    ) -> assert false (* cannot happen *)
    in
    match_args r.lhs stk
  in
  (* EXPE *)
  if List.length !(s.sym_rules) > 0 then
    begin
      Printf.printf "***************************\n" ;
      Printf.printf "Building tree for symb %s\n" (s.sym_name) ;
      let pama = Dtree.Pattmat.of_rules Timed.(!(s.sym_rules)) in
      let tree = compile pama in
      Dtree.to_dot s.sym_name tree ;
    end ;
  (* EXPE *)
  List.map_find match_rule Timed.(!(s.sym_rules))

(** [matching ar p t] checks that term [t] matches pattern [p]. The values for
    pattern variables (using the [ITag] node) are stored in [ar], at the index
    they denote. In case several different values are found for a same pattern
    variable, equality modulo is computed to check compatibility. *)
and matching : term_env array -> term -> stack_elt -> bool = fun ar p t ->
  if !log_enabled then
    log_eval "[%a] =~= [%a]" pp p pp (snd (Pervasives.(!t)));
  let res =
    (* First handle patterns that do not need the evaluated term. *)
    match p with
    | Patt(Some(i),_,[||]) when ar.(i) = TE_None ->
        let fn _ = snd Pervasives.(!t) in
        let b = Bindlib.raw_mbinder [||] [||] 0 mkfree fn in
        ar.(i) <- TE_Some(b); true
    | Patt(Some(i),_,e   ) when ar.(i) = TE_None ->
        let fn t = match t with Vari(x) -> x | _ -> assert false in
        let vars = Array.map fn e in
        let b = Bindlib.bind_mvar vars (lift (snd Pervasives.(!t))) in
        ar.(i) <- TE_Some(Bindlib.unbox b); Bindlib.is_closed b
    | Patt(None,_,[||]) -> true
    | Patt(None,_,e   ) ->
        let fn t = match t with Vari(x) -> x | _ -> assert false in
        let vars = Array.map fn e in
        let b = Bindlib.bind_mvar vars (lift (snd Pervasives.(!t))) in
        Bindlib.is_closed b
    | _                                 ->
    (* Other cases need the term to be evaluated. *)
    if not (fst Pervasives.(!t)) then Pervasives.(t := (true, whnf (snd !t)));
    match (p, snd Pervasives.(!t)) with
    | (Patt(Some(i),_,e), t            ) -> (* ar.(i) <> TE_None *)
        let b = match ar.(i) with TE_Some(b) -> b | _ -> assert false in
        eq_modulo (Bindlib.msubst b e) t
    | (Abst(_,t1)       , Abst(_,t2)   ) ->
        let (_,t1,t2) = Bindlib.unbind2 t1 t2 in
        matching ar t1 (Pervasives.ref (false, t2))
    | (Appl(t1,u1)      , Appl(t2,u2)  ) ->
        matching ar t1 (Pervasives.ref (fst Pervasives.(!t), t2))
        && matching ar u1 (Pervasives.ref (false, u2))
    | (Vari(x1)         , Vari(x2)     ) -> Bindlib.eq_vars x1 x2
    | (Symb(s1,_)       , Symb(s2,_)   ) -> s1 == s2
    | (_                , _            ) -> false
  in
  if !log_enabled then
    log_eval (r_or_g res "[%a] =~= [%a]") pp p pp (snd Pervasives.(!t));
  res

(** [eq_modulo a b] tests equality modulo rewriting between [a] and [b]. *)
and eq_modulo : term -> term -> bool = fun a b ->
  if !log_enabled then log_eqmd "[%a] == [%a]" pp a pp b;
  let rec eq_modulo l =
    match l with
    | []       -> ()
    | (a,b)::l ->
    let a = unfold a and b = unfold b in
    if a == b then eq_modulo l else
    match (whnf a, whnf b) with
    | (Patt(_,_,_), _          )
    | (_          , Patt(_,_,_))
    | (TEnv(_,_)  , _          )
    | (_          , TEnv(_,_)  )
    | (Kind       , _          )
    | (_          , Kind       ) -> assert false
    | (Type       , Type       ) -> eq_modulo l
    | (Vari(x1)   , Vari(x2)   ) when Bindlib.eq_vars x1 x2 -> eq_modulo l
    | (Symb(s1,_) , Symb(s2,_) ) when s1 == s2 -> eq_modulo l
    | (Prod(a1,b1), Prod(a2,b2))
    | (Abst(a1,b1), Abst(a2,b2)) ->
        let (_,b1,b2) = Bindlib.unbind2 b1 b2 in
        eq_modulo ((a1,a2)::(b1,b2)::l)
    | (Appl(t1,u1), Appl(t2,u2)) -> eq_modulo ((u1,u2)::(t1,t2)::l)
    | (Meta(m1,a1), Meta(m2,a2)) when m1 == m2 ->
        eq_modulo (if a1 == a2 then l else List.add_array2 a1 a2 l)
    | (_          , _          ) -> raise Exit
  in
  let res = try eq_modulo [(a,b)]; true with Exit -> false in
  if !log_enabled then log_eqmd (r_or_g res "%a == %a") pp a pp b; res

(** [specialize p m]  specializes the matrix [m] when matching against pattern
    [p].  A matrix can be specialized by a user defined symbol, an abstraction
    or a pattern variable.  The specialization always happen on the first
    column (which is swapped if needed). *)
and specialize : term -> Dtree.Pattmat.t -> Dtree.Pattmat.t = fun p m ->
  let filtered = List.filter (fun (l, _) ->
      (* Removed rules starting with a different constructor*)
      match p, List.hd l with
      | Symb(s, _), Symb(s', _)                   -> s = s'
      | Abst(_, b1), Abst(_, b2)                  ->
        let _, _, _ = Bindlib.unbind2 b1 b2 in
        true (* should be a matching env t1 t2*)
      (* We should check that bodies depend on the same variables. *)
      | Appl(_, _), Appl(_, _)                    -> true
      | Patt(Some(_), _, _), Patt(Some(_), _, _)  -> true
      (* Should be [matching env e.(i) d.(j)] *)
      | _                  , Patt(None, _, [| |]) -> true
      | Symb(_, _), Appl(_, _)                    -> false
      (* will be put in catch-all case*)
      | x                  , y ->
        begin
          Buffer.clear Format.stdbuf ; pp Format.str_formatter x ;
          pp Format.str_formatter y ;
          let msg = Printf.sprintf "%s: suspicious specialization-filtering"
              (Buffer.contents Format.stdbuf) in
          failwith msg
        end) m in
  let unfolded = List.map (fun (l, a) ->
      match p, List.hd l with
      | _                  , Symb(_, _)               ->
        (List.tl l, a) (* Eat the symbol? *)
      (* Checks could be done on arity of symb. *)
      | _                  , Abst(_, b)               ->
        let _, t = Bindlib.unbind b in (t :: List.tl l, a)
      | _                  , Appl(t1, t2)             ->
        (t1 :: t2 :: List.tl l, a)
        (* Might need to add wildcard to other lines. *)
      | Patt(None, _, [||]), Patt(None, _, [||]) as ws  ->
        ((fst ws) :: List.tl l, a)
      | Patt(None, _, e)   , Patt(None, _, [||]) as ws ->
        let ari = Array.length e in
        (List.init ari (fun _ -> snd ws) @ (List.tl l), a)
      | _                  , Patt(Some(_), _, _)      ->
        failwith "non linearity not yet implemented"
      | _                  , x                        ->
        Buffer.clear Format.stdbuf ; pp Format.str_formatter x ;
        let msg = Printf.sprintf "%s: suspicious specialization unfold"
            (Buffer.contents Format.stdbuf) in
        failwith msg) filtered in
  unfolded

(** [default m] computes the default matrix containing what remains to be
    matched if no specialization occurred. *)
and default : Dtree.Pattmat.t -> Dtree.Pattmat.t = fun m ->
  let filtered = List.filter (fun (l, _) ->
      match List.hd l with
      | Symb(_, _) | Abst(_, _) | Patt(Some(_), _, _) -> false
      | Patt(None , _, _) | Appl(_, _)                -> true
      | x                                             ->
        pp Format.err_formatter x ;
        assert false) m in
  let unfolded = List.map (fun (l, a) ->
      match List.hd l with
      | Patt(None, _, _) -> (List.tl l, a) (* Might be the only case *)
      | Appl(t1, t2)     -> (t1 :: t2 :: List.tl l, a)
      (* might need to add wildcards to other lines *)
      | _                -> assert false) filtered in
  unfolded

and compile : Dtree.Pattmat.t -> Dtree.t = fun m ->
  let module Pm = Dtree.Pattmat in
  let rec grow m =
    Pm.pp m ;
    if List.length m = 0 then (* If matrix is empty *)
      begin
        failwith "matching failure" ;
        (* Dtree.Fail *)
      end
    else
      (* Look at the first line, if it contains only wildcards, then
         execute the associated action. *)
      let fline = fst @@ List.hd m in
      if Pm.is_pattern_free fline then
        Dtree.Leaf(snd @@ List.hd m)
      else
        (* Pick a column in the matrix and pattern match on the constructors in
           it to grow the tree. *)
        let kept_cols = Pm.discard_patt_free m in
        print_newline () ; print_string "kept: " ;
        print_int_list (Array.to_list kept_cols) ; print_newline () ;
        let sel_in_partial = Pm.pick_best (Pm.select m kept_cols) in
        let swap = if kept_cols.(sel_in_partial) = 0 then None
          else Some kept_cols.(sel_in_partial) in
        Printf.printf "swap: %d\n" (match swap with None -> 0 | Some i -> i) ;
        (* XXX Perform swap!! *)
        let selected_c = match swap with
          | None   -> Pm.get_col 0 m
          | Some i -> Pm.get_col i m in
        Printf.printf "length selected col: %d\n" (List.length selected_c) ;
        let cons = List.filter (fun x -> match x with
            | Symb(_, _) | Abst(_, _) | Patt(Some(_), _, _)-> true
            | _                                            -> false)
            selected_c in
        Printf.printf "length %d\n" (List.length cons) ;
        let ms = List.map (fun s -> specialize s m) cons and
            defm = default m in
        let children = List.map grow
                         (if Pm.is_empty defm then ms else ms @ [defm]) in
        Node(swap, children) in
  grow m

let whnf : term -> term = fun t ->
  let t = unfold t in
  Pervasives.(steps := 0);
  let u = whnf t in
  if Pervasives.(!steps = 0) then t else u

(** [snf t] computes the strong normal form of the term [t]. *)
let rec snf : term -> term = fun t ->
  let h = whnf t in
  match h with
  | Vari(_)     -> h
  | Type        -> h
  | Kind        -> h
  | Symb(_)     -> h
  | Prod(a,b)   ->
      let (x,b) = Bindlib.unbind b in
      let b = snf b in
      let b = Bindlib.unbox (Bindlib.bind_var x (lift b)) in
      Prod(snf a, b)
  | Abst(a,b)   ->
      let (x,b) = Bindlib.unbind b in
      let b = snf b in
      let b = Bindlib.unbox (Bindlib.bind_var x (lift b)) in
      Abst(snf a, b)
  | Appl(t,u)   -> Appl(snf t, snf u)
  | Meta(m,ts)  -> Meta(m, Array.map snf ts)
  | Patt(_,_,_) -> assert false
  | TEnv(_,_)   -> assert false
  | Wild        -> assert false
  | TRef(_)     -> assert false

(** [hnf t] computes the head normal form of the term [t]. *)
let rec hnf : term -> term = fun t ->
  match whnf t with
  | Appl(t,u) -> Appl(hnf t, hnf u)
  | t         -> t

(** Type representing the different evaluation strategies. *)
type strategy = WHNF | HNF | SNF | NONE

(** Configuration for evaluation. *)
type config =
  { strategy : strategy   (** Evaluation strategy.          *)
  ; steps    : int option (** Max number of steps if given. *) }

(** [eval cfg t] evaluates the term [t] according to configuration [cfg]. *)
let eval : config -> term -> term = fun c t ->
  match (c.strategy, c.steps) with
  | (_   , Some(0))
  | (NONE, _      ) -> t
  | (WHNF, None   ) -> whnf t
  | (SNF , None   ) -> snf t
  | (HNF , None   ) -> hnf t
  (* TODO implement the rest. *)
  | (_   , Some(_)) -> wrn None "Number of steps not supported."; t
