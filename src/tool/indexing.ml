open Core open Term
open Common open Pos

type sym_name = Common.Path.t * string
let name_of_sym s = (s.sym_path, s.sym_name)

(* discrimination tree *)
(* substitution trees would be best *)

(* - all variables are mapped to HOLE
   - let-ins are expanded when indexed, but not when computing subterms
     to index
   - HOLES (i.e. variables, i.e. is_vari) are not indexed as subterms
*)

type 'a index =
 | Leaf of 'a list
 | Choice of 'a node list
and 'a node =
 | IHOLE of 'a index
 | IRigid of rigid * 'a index
and rigid =
 | IKind
 | IType
 | ISymb of sym_name
 | IAppl
 | IAbst
 | IProd

type 'a db = 'a list Lplib.Extra.StrMap.t * 'a index

let empty : 'a db =  Lplib.Extra.StrMap.empty, Choice []

let term_of_patt (_var, _varname, args) =
 let var = Bindlib.new_var mk_Vari "dummy" in
 Array.fold_left (fun t a -> mk_Appl (t,a)) (mk_Vari var) args

let rec node_of_stack t s v =
 match unfold t with
 | Kind -> IRigid(IKind, index_of_stack s v)
 | Type -> IRigid(IType, index_of_stack s v)
 | Vari _ -> IHOLE (index_of_stack s v)
 | Symb sym  -> IRigid(ISymb (name_of_sym sym), index_of_stack s v)
 | Appl(t1,t2) -> IRigid(IAppl, index_of_stack (t1::t2::s) v)
 | Abst(t1,bind) ->
    let _, t2 = Bindlib.unbind bind in
    IRigid(IAbst, index_of_stack (t1::t2::s) v)
 | Prod(t1,bind) ->
    let _, t2 = Bindlib.unbind bind in
    IRigid(IProd, index_of_stack (t1::t2::s) v)
 | Patt (_var,_varname,args) ->
     (* variable application, used in rewriting rules LHS *)
    node_of_stack (term_of_patt (_var,_varname,args)) s v
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
 | ISymb n, Symb sym  when n = name_of_sym sym -> []
 | IAppl, Appl(t1,t2) -> [t1;t2]
 | IAbst, Abst(t1,bind) ->
    let _, t2 = Bindlib.unbind bind in
    [t1;t2]
 | IProd, Prod(t1,bind) ->
    let _, t2 = Bindlib.unbind bind in
    [t1;t2]
 | _, Patt (_var,_varname,args) ->
     match_rigid r (term_of_patt (_var,_varname,args))
 | _, LLet (_typ, bod, bind) -> match_rigid r (Bindlib.subst bind bod)
 | _, (Meta _ | Plac _ | Wild | TRef _ | TEnv _) -> assert false
 | _, _ -> raise NoMatch

(* match anything with a flexible term *)
let rec match_flexible =
 function
    IHOLE i -> [i]
  | IRigid(r,i) ->
     match r with
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
 | IHOLE i, Vari _ -> IHOLE (insert_index i s v)
 | IRigid(r,i), t ->
    let s' = match_rigid r t in
    IRigid(r,insert_index i (s'@s) v)
 | _, _ -> raise NoMatch

let insert (namemap,index) term v =
 namemap, insert_index index [term] v

let insert_name (namemap,index) name v =
 let vs = match Lplib.Extra.StrMap.find_opt name namemap with None -> [] | Some l -> l in
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
let resolve_name (namemap,_) name =
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

module DB = struct
 type item =
  | Name of sym_name * Common.Pos.pos option
  | Type of sym_name * Common.Pos.pos option
  | InType of sym_name * Common.Pos.pos option

 let dbpath = "LPSearch.db"

 let restore_from_disk () =
  try
   restore_from ~filename:dbpath
  with
   Sys_error msg ->
     Common.Error.wrn None "Error loading DB. %s\nDefaulting to empty index"
      msg ;
     empty

 let db = ref (lazy (restore_from_disk ()))

 let empty () = db := lazy empty

 let insert k v =
   let db' = insert (Lazy.force !db) k v in
   db := lazy db'

 let insert_name k v =
   let db' = insert_name (Lazy.force !db) k v in
   db := lazy db'

 let search k = search (Lazy.force !db) k

 let dump () = dump_to ~filename:dbpath (Lazy.force !db)

 (*let restore_from ~filename = db := lazy (restore_from ~filename)*)

 let resolve_name name =
  resolve_name (Lazy.force !db) name

 let find_sym ~prt:_prt ~prv:_prv _sig_state {elt=(mp,name); pos} =
  let mp =
   match mp with
     [] ->
      (match resolve_name name with
          [Name ((mp,_),_)] -> mp
        | [] -> Common.Error.fatal pos "Unknown object %s." name
        | (Name((mp,_),_))::_ ->
           prerr_endline "OVERLOADED SYMBOL, PICKING FIRST INTERPRETATION";
           mp
        | _::_ -> assert false)
    | _::_ -> mp
  in
   Core.Term.create_sym mp Core.Term.Public Core.Term.Defin Core.Term.Sequen
    false (Common.Pos.make pos name) Core.Term.mk_Type []

 let pp_item_list =
  Lplib.List.pp
   (fun ppf item ->
     match item with
      | Name ((p,n),pos) ->
         Lplib.Base.out ppf "Name of %a.%s@%a@." Core.Print.path p n
          Common.Pos.pp pos
      | Type ((p,n),pos) ->
         Lplib.Base.out ppf "Type of %a.%s@%a@." Core.Print.path p n
          Common.Pos.pp pos
      | InType ((p,n),pos) ->
         Lplib.Base.out ppf "Strict subterm of the type of %a.%s@%a@."
          Core.Print.path p n Common.Pos.pp pos)
   "\n"

 let search_pterm pterm =
  let sig_state = Core.Sig_state.dummy in
  let env = [] in
  let query = Parsing.Scope.scope_lhs ~find_sym false sig_state env pterm in
  search query
end

module HL = struct
 let subterms_to_index t =
  let rec aux ?(top=false) t =
   (if top || Core.Term.is_vari t then [] else [t]) @
   match Core.Term.unfold t with
   | Vari _
   | Type
   | Kind
   | Symb _ -> []
   | Prod(t,b)
   | Abst(t,b) ->
      let _, t2 = Bindlib.unbind b in
      aux t @ aux t2
   | Appl(t1,t2) ->
      aux t1 @ aux t2
   | Patt (_var,_varname,args) ->
      (* variable application, used in rewriting rules LHS *)
      aux (term_of_patt (_var,_varname,args))
   | LLet (t1,t2,b) ->
      (* we do not expand the let-in when indexing subterms *)
      let _, t3 = Bindlib.unbind b in
      aux t1 @ aux t2 @ aux t3
   | Meta _
   | Plac _ -> assert false (* not for meta-closed terms *)
   | Wild -> assert false (* used only by tactics and reduction *)
   | TRef _  -> assert false (* destroyed by unfold *)
   | TEnv _ (* used in rewriting rules RHS *) ->
       assert false (* use term_of_rhs *)
  in aux ~top:true t

  (*
  { lhs      : term list (** Left hand side (LHS). *)
  ; rhs      : rhs (** Right hand side (RHS). *)
  ; arity    : int (** Required number of arguments to be applicable. *)
  ; arities  : int array
  (** Arities of the pattern variables bound in the RHS. *)
  ; vars     : tevar array
  (** Bindlib variables used to build [rhs]. The last [xvars_nb] variables
      appear only in [rhs]. *)
  ; xvars_nb : int (** Number of variables in [rhs] but not in [lhs]. *)
  ; rule_pos : Pos.popt (** Position of the rule in the source file. *) }
 *)
 let index_rule sym {Core.Term.lhs=lhsargs ; rhs ; rule_pos ; _} =
  let lhs = Core.Term.add_args (Core.Term.mk_Symb sym) lhsargs in
  let _ = (lhs,rhs,rule_pos) in
  ()(*
  DB.insert Timed.(!(sym.Core.Term.sym_type))
   ((name_of_sym sym),sym.sym_pos)*)

 let index_sym sym =
  let qname = name_of_sym sym in
  (* Name *)
  DB.insert_name (snd qname) (Name (qname,sym.sym_pos)) ;
  (* Type *)
  let typ = Timed.(!(sym.Core.Term.sym_type)) in
  DB.insert typ (Type (qname,sym.sym_pos)) ;
  (* InType *)
  let subterms = List.sort_uniq Core.Term.cmp (subterms_to_index typ) in
  List.iter (fun s -> DB.insert s (InType (qname,sym.sym_pos))) subterms ;
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

end
