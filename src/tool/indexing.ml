open Core.Term

type sym_name = Common.Path.t * string
let name_of_sym s = (s.sym_path, s.sym_name)

module StrMap = Map.Make(String)

(* discrimination tree *)
(* substitution trees would be best *)

(* - all variables are mapped to HOLE
   - let-ins are expanded
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

type 'a db = 'a list StrMap.t * 'a index

let empty =  StrMap.empty, Choice []

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
 | Patt (_var,_varname,args) -> (* variable application, used in rewriting rules LHS *)
    node_of_stack (term_of_patt (_var,_varname,args)) s v
 | LLet (_typ, bod, bind) ->
    (* Let-ins are expanded during indexing *)
    node_of_stack (Bindlib.subst bind bod) s v
 | Meta _
 | Plac _ -> assert false (* not for meta-closed terms *)
 | Wild -> assert false (* used only by tactics and reduction *)
 | TRef _  -> assert false (* destroyed by unfold *)
 | TEnv _ (* used in rewriting rules RHS *) -> assert false (* use term_of_rhs *)
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
 | _, Patt (_var,_varname,args) -> match_rigid r (term_of_patt (_var,_varname,args))
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
      | IProd -> List.concat (List.map match_flexible_index (match_flexible_index i))
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

let insert symname_of (namemap,index) term v =
 let name = symname_of v in
 let vs = match StrMap.find_opt name namemap with None -> [] | Some l -> l in
 StrMap.add name (v::vs) namemap, insert_index index [term] v

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
     prerr_endline "FLESSIBILE" ;
     List.concat (List.map (fun i -> search_index i s) (match_flexible node))
 | IHOLE i, _ -> search_index i s
 | IRigid(r,i), t ->
     match match_rigid r t with
     | s' -> search_index i (s'@s)
     | exception NoMatch -> []

let search (_,index) term = search_index index [term]
let resolve_name (namemap,_) name =
  match StrMap.find_opt name namemap with None -> [] | Some l -> l

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
 type item = sym_name * Common.Pos.pos option
 let db = ref empty
 let insert k v =
   db := insert (fun ((_,name),_) -> name) !db k v(*;
   let vs = search !db k in
   prerr_endline "XXXXXXXXXXXXXXXXXXX" ;
   Format.printf "Indexing %a@." Core.Print.term k ;
   List.iter
    (fun ((p,n),pos) -> Format.printf "Equivalent to %a.%s@%a@." Core.Print.path p n Common.Pos.pp pos)
    vs ;
   prerr_endline ("")
*)
 let search k = search !db k
 let dump_to ~filename = dump_to ~filename !db
 let restore_from ~filename = db := restore_from ~filename
 let resolve_name name = resolve_name !db name
end
