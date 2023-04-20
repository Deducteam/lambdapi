open Core open Term
open Common open Pos

type sym_name = Common.Path.t * string
let name_of_sym s = (s.sym_path, s.sym_name)

(* discrimination tree *)
(* substitution trees would be best *)

(* - all variables are indexed equally, ignoring the name
   - let-ins are expanded when indexed, but not when computing subterms
     to index
   - patterns (e.g. $x.[t1 .. tn]) are indexed as HOLES, ignoring the
     arguments t1 .. tn
   - we consider t1 ... tn as subterms when computing the subterms to index
   - flexible terms, i.e. applyed HOLES (i.e. applied patterns $x.[t1 .. tn])
     are not indexed as subterms
   - when computing the subterms to index, when entering a product the
     bound variable is replaced with a pattern to simulate modus-ponens
     e.g. "pi x : T. x + x"  has as subterm "$x + $x"
*)

module Pure = struct

type 'a index =
 | Leaf of 'a list
 | Choice of 'a node list
and 'a node =
 | IHOLE of 'a index
 | IRigid of rigid * 'a index
and rigid =
 | IVar
 | IKind
 | IType
 | ISymb of sym_name
 | IAppl
 | IAbst
 | IProd

type 'a db = 'a list Lplib.Extra.StrMap.t * 'a index

let empty : 'a db =  Lplib.Extra.StrMap.empty, Choice []

(* unused
let term_of_patt (_var, _varname, args) =
 let var = Bindlib.new_var mk_Vari "dummy" in
 Array.fold_left (fun t a -> mk_Appl (t,a)) (mk_Vari var) args
*)

let rec node_of_stack t s v =
 match unfold t with
 | Kind -> IRigid(IKind, index_of_stack s v)
 | Type -> IRigid(IType, index_of_stack s v)
 | Vari _ -> IRigid(IVar, index_of_stack s v)
 | Symb sym  -> IRigid(ISymb (name_of_sym sym), index_of_stack s v)
 | Appl(t1,t2) -> IRigid(IAppl, index_of_stack (t1::t2::s) v)
 | Abst(t1,bind) ->
    let _, t2 = Bindlib.unbind bind in
    IRigid(IAbst, index_of_stack (t1::t2::s) v)
 | Prod(t1,bind) ->
    let _, t2 = Bindlib.unbind bind in
    IRigid(IProd, index_of_stack (t1::t2::s) v)
 | Patt (_var,_varname,_args) ->
    IHOLE (index_of_stack s v)
 | LLet (_typ, bod, bind) ->
    (* Let-ins are expanded during indexing *)
    node_of_stack (Bindlib.subst bind bod) s v
 | Meta _
 | Plac _ -> assert false (* not for meta-closed terms *)
 | Wild -> assert false (* used only by tactics and reduction *)
 | TRef _  -> assert false (* destroyed by unfold *)
 | TEnv _ (* used in rewriting rules RHS *) ->
     assert false (* use term_of_rhs *)
and index_of_stack stack v =
 match stack with
 | [] -> Leaf [v]
 | t::s -> Choice [node_of_stack t s v]

exception NoMatch

(* match a rigid with a term, either raising NoMatch or returning the
   (ordered) list of immediate subterms of the term *)
let rec match_rigid r term =
 match r,unfold term with
 | IKind, Kind -> []
 | IType, Type -> []
 | IVar, Vari _ -> []
 | ISymb n, Symb sym  when n = name_of_sym sym -> []
 | IAppl, Appl(t1,t2) -> [t1;t2]
 | IAbst, Abst(t1,bind) ->
    let _, t2 = Bindlib.unbind bind in
    [t1;t2]
 | IProd, Prod(t1,bind) ->
    let _, t2 = Bindlib.unbind bind in
    [t1;t2]
 | _, LLet (_typ, bod, bind) -> match_rigid r (Bindlib.subst bind bod)
 | _, (Meta _ | Plac _ | Wild | TRef _ | TEnv _) -> assert false
 | _, _ -> raise NoMatch

(* match anything with a flexible term *)
let rec match_flexible =
 function
    IHOLE i -> [i]
  | IRigid(r,i) ->
     match r with
      | IVar
      | IKind
      | IType
      | ISymb _ -> [i]
      | IAppl
      | IAbst
      | IProd ->
          List.concat (List.map match_flexible_index (match_flexible_index i))
and match_flexible_index =
 function
    Leaf _ -> assert false (* ill-typed term *)
  | Choice nodes ->
     List.concat (List.map match_flexible nodes)

let rec insert_index index stack v =
 match index,stack with
 | Leaf vs, [] -> Leaf(v::vs)
 | Choice l, t::s ->
    let rec aux =
     function
     | [] -> [node_of_stack t s v]
     | n::nl ->
       try
        insert_node n t s v :: nl
       with
        NoMatch -> n :: aux nl
    in Choice(aux l)
 | _, _ -> assert false (* ill-typed term *)
and insert_node node term s v =
 match node,term with
 (* Patterns are holes, holes are patterns *)
 | IHOLE i, Patt _ -> IHOLE (insert_index i s v)
 | IRigid(r,i), t ->
    let s' = match_rigid r t in
    IRigid(r,insert_index i (s'@s) v)
 | _, _ -> raise NoMatch

let insert (namemap,index) term v =
 namemap, insert_index index [term] v

let insert_name (namemap,index) name v =
 let vs =
  match Lplib.Extra.StrMap.find_opt name namemap with
     None -> []
   | Some l -> l in
 Lplib.Extra.StrMap.add name (v::vs) namemap, index

let rec search_index index stack =
 match index,stack with
 | Leaf vs, [] -> vs
 | Choice l, t::s ->
    List.fold_right
     (fun n res -> search_node n t s @ res) l []
 | _, _ -> assert false (* ill-typed term *)
and search_node node term s =
 match node,term with
 | _, Patt _ ->
     List.concat (List.map (fun i -> search_index i s) (match_flexible node))
 | IHOLE i, _ -> search_index i s
 | IRigid(r,i), t ->
     match match_rigid r t with
     | s' -> search_index i (s'@s)
     | exception NoMatch -> []

let search (_,index) term = search_index index [term]
let locate_name (namemap,_) name =
  match Lplib.Extra.StrMap.find_opt name namemap with None -> [] | Some l -> l

let dump_to ~filename i =
 let ch = open_out_bin filename in
 Marshal.to_channel ch i [] ;
 close_out ch

let restore_from ~filename =
  let ch = open_in_bin filename in
  let i = Marshal.from_channel ch in
  close_in ch ;
  i

end

module DB = struct
 (* fix codomain type *)

 type side = Lhs | Rhs
 type match_type = Exact | Inside
 type item =
  | Name of sym_name * Common.Pos.pos option
  | Type of match_type * sym_name * Common.Pos.pos option
  | Xhs of side * match_type * Common.Pos.pos

 let pp_side fmt =
  function
   | Lhs -> Lplib.Base.out fmt "lhs"
   | Rhs -> Lplib.Base.out fmt "rhs"

 let pp_item_list =
  Lplib.List.pp
   (fun ppf item ->
     match item with
      | Name ((p,n),pos) ->
         Lplib.Base.out ppf "Name of %a.%s@%a@." Core.Print.path p n
          Common.Pos.pp pos
      | Type (Exact,(p,n),pos) ->
         Lplib.Base.out ppf "Type of %a.%s@%a@." Core.Print.path p n
          Common.Pos.pp pos
      | Type (Inside,(p,n),pos) ->
         Lplib.Base.out ppf "Strict subterm of the type of %a.%s@%a@."
          Core.Print.path p n Common.Pos.pp pos
      | Xhs (side,Exact,pos) ->
         Lplib.Base.out ppf "The %a of %a@." pp_side side
          Common.Pos.pp (Some pos)
      | Xhs (side,Inside,pos) ->
         Lplib.Base.out ppf "Inside %a of %a@." pp_side side
          Common.Pos.pp (Some pos))
   ""

 (* disk persistence *)

 let dbpath = "LPSearch.db"
 let rwpath = "LPSearch.dk"

 let restore_from_disk () =
  try
   Pure.restore_from ~filename:dbpath
  with
   Sys_error msg ->
     Common.Error.wrn None "Error loading DB. %s\nDefaulting to empty index"
      msg ;
     Pure.empty

 let db : item Pure.db Lazy.t ref = ref (lazy (restore_from_disk ()))

 let empty () = db := lazy Pure.empty

 let insert k v =
   let db' = Pure.insert (Lazy.force !db) k v in
   db := lazy db'

 let insert_name k v =
   let db' = Pure.insert_name (Lazy.force !db) k v in
   db := lazy db'

 let search k = Pure.search (Lazy.force !db) k

 let dump () = Pure.dump_to ~filename:dbpath (Lazy.force !db)

 let locate_name name =
  Pure.locate_name (Lazy.force !db) name

end

let find_sym ~prt:_prt ~prv:_prv _sig_state {elt=(mp,name); pos} =
 let mp =
  match mp with
    [] ->
     (match DB.locate_name name with
         [DB.Name ((mp,_),_)] -> mp
       | [] -> Common.Error.fatal pos "Unknown object %s." name
       | (DB.Name((mp,_),_))::_ ->
          Common.Error.wrn pos
           "Overloaded symbol %s, choosing the one declared in %a" name
            Common.Path.pp mp ;
          mp
       | _::_ -> assert false)
   | _::_ -> mp
 in
  Core.Term.create_sym mp Core.Term.Public Core.Term.Defin Core.Term.Sequen
   false (Common.Pos.make pos name) Core.Term.mk_Type []

let search_pterm pterm =
 let sig_state = Core.Sig_state.dummy in
 let env = [] in
 let query = Parsing.Scope.scope_lhs ~find_sym false sig_state env pterm in
 DB.search query

module QNameMap =
 Map.Make(struct type t = sym_name let compare = Stdlib.compare end)

let check_rule : Parsing.Syntax.p_rule -> sym_rule = fun r ->
 let ss = Core.Sig_state.dummy in
 let pr = Parsing.Scope.scope_rule ~find_sym false ss r in
 let s = pr.elt.pr_sym in
 let r = Parsing.Scope.rule_of_pre_rule pr in
 s, r

let load_meta_rules () =
 let cmdstream =
   Parsing.Parser.Dk.parse_file DB.rwpath in
 let rules = ref [] in
 Stream.iter
  (fun {elt ; _ } ->
    match elt with
      Parsing.Syntax.P_rules r -> rules := List.rev_append r !rules
    | _ -> ())
  cmdstream ;
 let rules = List.rev !rules in
 let handle_rule map r =
   let (s,r) = check_rule r in
   let h = function Some rs -> Some(r::rs) | None -> Some[r] in
   SymMap.update s h map in
 let map = List.fold_left handle_rule SymMap.empty rules in
 SymMap.iter Tree.update_dtree map;
 SymMap.fold
  (fun sym _rs map' ->
    QNameMap.add (name_of_sym sym) (Timed.(!(sym.sym_dtree))) map')
  map QNameMap.empty

let meta_rules = lazy (load_meta_rules ())

let normalize typ =
 let dtree sym =
  try
   QNameMap.find (name_of_sym sym) (Lazy.force meta_rules)
  with
   Not_found -> Core.Tree_type.empty_dtree in
 Core.Eval.snf ~dtree ~tags:[`NoExpand] [] typ

let rec is_flexible t =
 match Core.Term.unfold t with
  | Patt _ -> true
  | Appl(t,_) -> is_flexible t
  | LLet(_,_,b) ->
     let _, t = Bindlib.unbind b in
     is_flexible t
  | Vari _ | Type | Kind | Symb _ | Prod _ | Abst _ -> false
  | Meta _
  | Plac _ -> assert false (* not for meta-closed terms *)
  | Wild -> assert false (* used only by tactics and reduction *)
  | TRef _  -> assert false (* destroyed by unfold *)
  | TEnv _ (* used in rewriting rules RHS *) ->
      assert false (* use term_of_rhs *)

let subterms_to_index t =
 let rec aux ?(top=false) ?(spine=false) t =
  let t = Core.Term.unfold t in
  (if top then [] else [t]) @
  match t with
  | Vari _
  | Type
  | Kind
  | Symb _ -> []
  | Abst(t,b) ->
     let _, t2 = Bindlib.unbind b in
     aux t @ aux t2
  | Prod(t,b) ->
     if spine then
      aux t @
       aux ~spine:true
        (Bindlib.subst b (Core.Term.mk_Patt (None,"dummy",[||])))
     else
      let _, t2 = Bindlib.unbind b in
      aux t @ aux t2
  | Appl(t1,t2) ->
     aux t1 @ aux t2
  | Patt (_var,_varname,args) ->
     List.concat (List.map aux (Array.to_list args))
  | LLet (t1,t2,b) ->
     (* we do not expand the let-in when indexing subterms *)
     let _, t3 = Bindlib.unbind b in
     aux t1 @ aux t2 @ aux ~spine:true t3
  | Meta _
  | Plac _ -> assert false (* not for meta-closed terms *)
  | Wild -> assert false (* used only by tactics and reduction *)
  | TRef _  -> assert false (* destroyed by unfold *)
  | TEnv _ (* used in rewriting rules RHS *) ->
      assert false (* use term_of_rhs *)
 in aux ~top:true ~spine:true t

let insert_rigid t v =
 if not (is_flexible t) then
  DB.insert t v

let index_rule sym ({Core.Term.lhs=lhsargs ; rule_pos ; _} as rule) =
 let rule_pos = match rule_pos with None -> assert false | Some pos -> pos in
 let lhs = Core.Term.add_args (Core.Term.mk_Symb sym) lhsargs in
 let rhs = Core.Term.term_of_rhs rule in
 let _ = (lhs,rhs,rule_pos) in
 let lhs = normalize lhs in
 let rhs = normalize rhs in
 insert_rigid lhs (Xhs(Lhs,Exact,rule_pos)) ;
 insert_rigid rhs (Xhs(Rhs,Exact,rule_pos)) ;
 let sublhs = List.sort_uniq Core.Term.cmp (subterms_to_index lhs) in
 List.iter (fun s -> insert_rigid s (Xhs (Lhs,Inside,rule_pos))) sublhs ;
 let subrhs = List.sort_uniq Core.Term.cmp (subterms_to_index rhs) in
 List.iter (fun s -> insert_rigid s (Xhs (Rhs,Inside,rule_pos))) subrhs

let index_sym sym =
 let qname = name_of_sym sym in
 (* Name *)
 DB.insert_name (snd qname) (Name (qname,sym.sym_pos)) ;
 (* Type *)
 let typ as _typ' = Timed.(!(sym.Core.Term.sym_type)) in
 let typ = normalize typ in
 (*
 Format.printf "%a.%s : %a REWRITTEN TO %a@."
  Core.Print.path (fst (name_of_sym sym)) (snd (name_of_sym sym))
  Core.Print.term typ' Core.Print.term typ ;
 *)
 insert_rigid typ (Type (Exact,qname,sym.sym_pos)) ;
 (*
 assert (List.mem (DB.Type (Exact,qname,sym.sym_pos)) (DB.search typ));
 *)
 (* InType *)
 let subterms = List.sort_uniq Core.Term.cmp (subterms_to_index typ) in
 List.iter (fun s -> insert_rigid s (Type (Inside,qname,sym.sym_pos)))
  subterms ;
 (* InBody??? sym.sym_def : term option ref
    but all the subterms are too much; collect only the constants? *)
 (* Rules *)
 List.iter (index_rule sym) Timed.(!(sym.Core.Term.sym_rules))

let index_sign sign =
 let syms = Timed.(!(sign.Core.Sign.sign_symbols)) in
 let rules = Timed.(!(sign.Core.Sign.sign_deps)) in
 Lplib.Extra.StrMap.iter (fun _ sym -> index_sym sym) syms ;
 Common.Path.Map.iter
  (fun path rules ->
    Lplib.Extra.StrMap.iter
     (fun name rules ->
       let sym = Core.Sign.find_sym path name in
       List.iter (index_rule sym) rules)
     rules)
  rules

(* let's flatten the interface *)
include DB
