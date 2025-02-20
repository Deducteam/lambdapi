open Syntax
open Common open Pos open Error
open Lplib

(** [get_args t] decomposes the parser level term [t] into a spine [(h,args)],
    when [h] is the term at the head of the application and [args] is the list
    of all its arguments.  The arguments are stored together with the position
    of the corresponding application node in the source code. Note that [h] is
    guaranteed not to be a [P_Appl] node. Term constructors with no equivalent
    in the dk syntax (like binary symbol applications) are not handled. *)
let get_args : p_term -> p_term * (popt * p_term) list = fun t ->
  let rec get_args acc t =
    match t.elt with
    | P_Appl(u,v) -> get_args ((t.pos,v)::acc) u
    | _           -> (t, acc)
  in get_args [] t

(** [add_args t args] builds the application of the term [t] to the  arguments
    [args]. When [args] is empty, the returned value is exactly [t]. Note that
    this function is the inverse of [get_args] (in some sense). *)
let add_args : p_term -> (popt * p_term) list -> p_term =
  List.fold_left (fun t (p,u) -> Pos.make p (P_Appl(t,u)))

(** Representation of a reduction rule, with its context. *)
type p_dk_rule = ((strloc * p_term option) list * p_term * p_term) loc

(** [to_p_rule r] transforms the dk representation of a rule into
    the lp representation. *)
let to_p_rule : p_dk_rule -> p_rule = fun r ->
  let (ctx, lhs, rhs) = r.elt in
  (* Check for (deprecated) annotations in the context. *)
  let get_var (x,ao) =
    let fn a = wrn a.pos "Ignored type annotation." in
    Option.iter fn ao; x
  in
  let ctx = List.map get_var ctx in
  let is_pat_var env x =
    not (List.mem x env) && List.exists (fun y -> y.elt = x) ctx
  in
  (* Find the maximum number of arguments a variable is applied to. *)
  let arity = Hashtbl.create 7 in
  let rec compute_arities env t =
    let (h, args) = get_args t in
    let nb_args = List.length args in
    begin
      match h.elt with
      | P_Appl(_,_)       -> assert false (* Cannot happen. *)
      | P_Iden(x,_)       ->
          let (p,x) = x.elt in
          if p = [] && is_pat_var env x then
            begin
              try
                let n = Hashtbl.find arity x in
                if nb_args > n then Hashtbl.replace arity x nb_args
              with Not_found -> Hashtbl.add arity x nb_args
            end
      | P_Wild            -> ()
      | P_Type            -> fatal h.pos "Type in dk pattern."
      | P_Prod(_,_)       -> fatal h.pos "Product in dk pattern."
      | P_Abst(xs,t)      ->
          begin
            match xs with
            | [(_       ,Some(a),_)] ->
                fatal a.pos "Annotation in dk pattern."
            | [([Some x],None   ,_)] ->
                compute_arities (x.elt::env) t
            | [([None  ],None   ,_)] ->
                compute_arities env t
            | _                      -> assert false
          end
      | P_Arro(_,_)       -> fatal h.pos "Implication in dk pattern."
      | P_LLet(_,_,_,_,_) -> fatal h.pos "Let expression in dk rule."
      | P_Meta(_,_)       -> assert false
      | P_Patt(_,_)       -> assert false
      | P_NLit(_)         -> assert false
      | P_SLit(_)         -> assert false
      | P_Wrap(_)         -> assert false
      | P_Expl(_)         -> assert false
    end;
    List.iter (fun (_,t) -> compute_arities env t) args
  in
  compute_arities [] lhs;
  (* Check that all context variables occur in the LHS. *)
  let check_here x =
    try ignore (Hashtbl.find arity x.elt) with Not_found ->
      fatal x.pos "Variable [%s] does not occur in the LHS." x.elt
  in
  List.iter check_here ctx;
  (* Actually process the LHS and RHS. *)
  let rec build env t =
    let (h, lts) = get_args t in
    match h.elt with
    | P_Iden({elt = ([],x); _}, _) when is_pat_var env x ->
        let lts = List.map (fun (p, t) -> (p, build env t)) lts in
        let max = try Hashtbl.find arity x with Not_found -> assert false in
        let k = List.length lts in
        (* Number of η-expansions required. *)
        let nb_exp = if k >= max then 0 else max - k in
        let p = t.pos in
        if nb_exp = 0 then
          (* No η-expansion required (enough arguments). *)
          let (lts1, lts2) = List.cut lts max in
          let ts1 = Array.of_list (List.map snd lts1) in
          let patt = Pos.make p (P_Patt(Some(Pos.make h.pos x), Some ts1)) in
          add_args patt lts2
        else
          (* We need to η-expense (not enough arguments). *)
          let ts = Array.of_list (List.map snd lts) in
          (* Create fresh variables. *)
          let ctx = List.map (fun x -> x.elt) ctx in
          (* Function to create fresh variable names. *)
          let new_var_name : unit -> string =
            let counter = ref (-1) in
            fun () ->
              incr counter;
              while List.mem (Printf.sprintf "v%i" !counter) ctx do
                incr counter
              done;
              Printf.sprintf "v%i" !counter
          in
          let vars = Array.init nb_exp (fun _ -> new_var_name ()) in
          (* Build the pattern. *)
          let fn x = Pos.none (P_Iden(Pos.none ([],x), false)) in
          let args = Array.append ts (Array.map fn vars) in
          let patt = Pos.make p (P_Patt(Some(Pos.make h.pos x), Some args)) in
          (* Build the abstraction. *)
          let xs = Array.map (fun x -> Some(Pos.none x)) vars in
          Pos.make p (P_Abst([Array.to_list xs, None, false], patt))
    | P_Wild when lts = [] && env = []                   -> t
    | P_Wild                                             ->
        let lts = List.map (fun (_, t) -> build env t) lts in
        Pos.make t.pos (P_Patt(None, Some (Array.of_list lts)))
    | _                                                  ->
    match t.elt with
    | P_Iden(_)
    | P_Type
    | P_Wild            -> t
    | P_Prod(xs,b)      ->
        let (x,a) =
          match xs with
          | [([Some x],Some(a),_)] -> (x, build env a)
          | _                      -> assert false (* Unreachable. *)
        in
        let b = build (x.elt::env) b in
        Pos.make t.pos (P_Prod([([Some x],Some(a),false)], b))
    | P_Arro(a,b)       -> Pos.make t.pos (P_Arro(build env a, build env b))
    | P_Abst(xs,u)      ->
        let (x,a) =
          match xs with
          | [([x],ao,_)] -> (x, Option.map (build env) ao)
          | _            -> assert false (* Unreachable. *)
        in
        let u =
          match x with
          | Some(x) -> build (x.elt::env) u
          | None    -> build env u
        in
        Pos.make t.pos (P_Abst([([x],a,false)], u))
    | P_Appl(t1,t2)     -> Pos.make t.pos (P_Appl(build env t1, build env t2))
    | P_Meta(_,_)       -> fatal t.pos "Invalid dk rule syntax."
    | P_Patt(_,_)       -> fatal h.pos "Pattern in dk rule."
    | P_LLet(_,_,_,_,_) -> fatal h.pos "Let expression in dk rule."
    | P_NLit(_)         -> fatal h.pos "Nat literal in dk rule."
    | P_SLit(_)         -> fatal h.pos "String literal in dk rule."
    | P_Wrap(_)         -> fatal h.pos "Wrapping constructor in dk rule."
    | P_Expl(_)         -> fatal h.pos "Explicit argument in dk rule."
  in
  (* NOTE the computation order is important for setting arities properly. *)
  let lhs = build [] lhs in
  let rhs = build [] rhs in
  Pos.make r.pos (lhs, rhs)
