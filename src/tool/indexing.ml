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

let rec search_index ~holes_in_index index stack =
 match index,stack with
 | Leaf vs, [] -> vs
 | Choice l, t::s ->
    List.fold_right
     (fun n res -> search_node ~holes_in_index n t s @ res) l []
 | _, _ -> assert false (* ill-typed term *)
and search_node ~holes_in_index node term s =
 match node,term with
 | _, Patt _ ->
     List.concat
      (List.map
        (fun i -> search_index ~holes_in_index i s) (match_flexible node))
 | IHOLE i, _ when holes_in_index -> search_index ~holes_in_index i s
 | IHOLE i, t -> search_node ~holes_in_index (IRigid(IVar,i)) t s
 | IRigid(r,i), t ->
     match match_rigid r t with
     | s' -> search_index ~holes_in_index i (s'@s)
     | exception NoMatch -> []

(* when [~holes_in_index] is fase, all holes in the index are matched
   only by variables *)
let search ~holes_in_index (_,index) term =
 search_index ~holes_in_index index [term]
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
 type inside = Exact | Inside
 type where =
  | Spine of inside
  | Conclusion of inside
  | Hypothesis of inside
 type item =
  | Name of                 sym_name * Common.Pos.pos option
  | Type of where         * sym_name * Common.Pos.pos option
  | Xhs  of inside * side *            Common.Pos.pos

 let pp_side fmt =
  function
   | Lhs -> Lplib.Base.out fmt "lhs"
   | Rhs -> Lplib.Base.out fmt "rhs"

 let pp_inside fmt =
  function
    | Exact -> Lplib.Base.out fmt "The exact"
    | Inside -> Lplib.Base.out fmt "Inside the"

 let pp_where fmt =
  function
   | Spine ins -> Lplib.Base.out fmt "%a spine of" pp_inside ins
   | Hypothesis ins -> Lplib.Base.out fmt "%a hypothesis of" pp_inside ins
   | Conclusion ins -> Lplib.Base.out fmt "%a conclusion of" pp_inside ins

 module ItemSet =
  Set.Make(struct type t = item let compare = compare end)

 let generic_pp_of_item_list ~separator ~delimiters ~lis:(lisb,lise)
  ~pres:(preb,pree)
 =
  Lplib.List.pp
   (fun ppf item ->
     match item with
      | Name ((p,n),pos) ->
         Lplib.Base.out ppf "%sName of %a.%s@%a%s%s%a%s%s@."
          lisb Core.Print.path p n Common.Pos.pp pos separator
           preb (Common.Pos.deref ~separator ~delimiters) pos pree lise
      | Type (where,(p,n),pos) ->
         Lplib.Base.out ppf
          "%s%a the type of %a.%s@%a%s%s%a%s%s@."
          lisb pp_where where Core.Print.path p n Common.Pos.pp pos
          separator preb (Common.Pos.deref ~separator ~delimiters) pos pree
          lise
      | Xhs (inside,side,pos) ->
         Lplib.Base.out ppf "%s%a %a of %a%s%s%a%s%s@."
          lisb pp_inside inside pp_side side Common.Pos.pp (Some pos)
          separator preb (Common.Pos.deref ~separator ~delimiters) (Some pos)
          pree lise)
   ""

 let html_of_item_list =
  generic_pp_of_item_list ~separator:"<br>\n" ~delimiters:("<p>","</p>")
   ~lis:("<li>","</li>") ~pres:("<pre>","</pre>")

 let pp_item_list =
  generic_pp_of_item_list ~separator:"\n" ~delimiters:("","")
   ~lis:("* ","") ~pres:("","")

 let pp_item_set fmt set = pp_item_list fmt (ItemSet.elements set)

 let html_of_item_set fmt set =
  Lplib.Base.out fmt "<ul>%a</ul>" html_of_item_list (ItemSet.elements set)

 (* disk persistence *)

 let dbpath = "LPSearch.db"
 let rwpath = "LPSearch.lp"

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

 let search ~holes_in_index  k =
  ItemSet.of_list (Pure.search ~holes_in_index  (Lazy.force !db) k)

 let dump () = Pure.dump_to ~filename:dbpath (Lazy.force !db)

 let locate_name name =
  ItemSet.of_list (Pure.locate_name (Lazy.force !db) name)

end

let find_sym ~prt:_prt ~prv:_prv _sig_state {elt=(mp,name); pos} =
 let mp =
  match mp with
    [] ->
     let res = DB.locate_name name in
     (match DB.ItemSet.choose_opt res with
       | None -> Common.Error.fatal pos "Unknown symbol %s." name
       | Some (DB.Name ((mp,_),_)) ->
          if DB.ItemSet.cardinal res > 1 then
           Common.Error.wrn pos
            "Overloaded symbol %s, choosing the one declared in %a" name
             Common.Path.pp mp ;
           mp
       | Some _ -> assert false) (* locate only returns DB.Name*)
  | _::_ -> mp
 in
  Core.Term.create_sym mp Core.Term.Public Core.Term.Defin Core.Term.Sequen
   (* CSC: TODO XXX is the position below wrong? It should come from
      locate_name! *)
   false (Common.Pos.make pos name) None Core.Term.mk_Type []

let search_pterm ~holes_in_index ~mok env pterm =
 let sig_state = Core.Sig_state.dummy in
 let env =
  ("V#",(Bindlib.new_var mk_Vari "V#" ,Bindlib.box Term.mk_Type,None))::env in
 let query =
  Parsing.Scope.scope_search_pattern ~find_sym ~mok sig_state env pterm in
 DB.search ~holes_in_index query

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
   Parsing.Parser.Lp.parse_file DB.rwpath in
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
  | Meta _ | Plac _ | Wild | TRef _ | TEnv _ -> assert false

let enter =
 DB.(function
  | Hypothesis _ -> Hypothesis Inside
  | Spine _
  | Conclusion _ -> Conclusion Inside)

let enter_pi_source =
 DB.(function
  | Spine _ -> Hypothesis Exact
  | Hypothesis _ -> Hypothesis Inside
  | Conclusion _ -> Conclusion Inside)

let enter_pi_target ~is_prod =
 DB.(function
  | Spine _ when is_prod -> Spine Inside
  | Spine _ -> Conclusion Exact
  | Hypothesis _ -> Hypothesis Inside
  | Conclusion _ -> Conclusion Inside)

let subterms_to_index ~is_spine t =
 let rec aux ~where t =
  let t = Core.Term.unfold t in
  [where,t] @
  match t with
  | Vari _
  | Type
  | Kind
  | Symb _ -> []
  | Abst(t,b) ->
     let _, t2 = Bindlib.unbind b in
     aux ~where:(enter where) t @ aux ~where:(enter where) t2
  | Prod(t,b) ->
     (match where with
       | Spine _ ->
          let t2 = Bindlib.subst b (Core.Term.mk_Patt (None,"dummy",[||])) in
          aux ~where:(enter_pi_source where) t @
           aux ~where:(enter_pi_target ~is_prod:(Core.Term.is_prod t2) where)
            t2
       | _ ->
         let _, t2 = Bindlib.unbind b in
         aux ~where:(enter_pi_source where) t @
          aux ~where:(enter_pi_target ~is_prod:false where) t2)
  | Appl(t1,t2) ->
     aux ~where:(enter where) t1 @ aux ~where:(enter where) t2
  | Patt (_var,_varname,args) ->
     List.concat (List.map (aux ~where:(enter where)) (Array.to_list args))
  | LLet (t1,t2,b) ->
     (* we do not expand the let-in when indexing subterms *)
     let _, t3 = Bindlib.unbind b in
     aux ~where:(enter where) t1 @ aux ~where:(enter where) t2 @
      aux ~where:(enter where) t3
  | Meta _ | Plac _ | Wild | TRef _ | TEnv _ -> assert false
 in aux ~where:(if is_spine then Spine Exact else Conclusion Exact) t

let insert_rigid t v =
 if not (is_flexible t) then begin
  DB.insert t v
  (* assert (List.mem v (DB.search t)); *)
 end

let index_term_and_subterms ~is_spine t item =
 let tn = normalize t in
 (*
 Format.printf "%a : %a REWRITTEN TO %a@."
  pp_item (item Exact) Core.Print.term t Core.Print.term tn ;
 *)
 let cmp (where1,t1) (where2,t2) =
  let res = compare where1 where2 in
  if res = 0 then Core.Term.cmp t1 t2 else res in
 let subterms =
  List.sort_uniq cmp (subterms_to_index ~is_spine tn) in
 List.iter (fun (where,s) -> insert_rigid s (item where)) subterms

let index_rule sym ({Core.Term.lhs=lhsargs ; rule_pos ; _} as rule) =
 let rule_pos =
   match rule_pos with
    | None -> assert false (* this probably may happen, but it is BAD!
                              I leave the assert false to detect when it
                              happens and let the team decide what to do *)
    | Some pos -> pos in
 let lhs = Core.Term.add_args (Core.Term.mk_Symb sym) lhsargs in
 let rhs = Core.Term.term_of_rhs rule in
 let _ = (lhs,rhs,rule_pos) in
 let get_inside = function | DB.Conclusion ins -> ins | _ -> assert false in
 index_term_and_subterms ~is_spine:false lhs
  (fun where -> (Xhs(get_inside where,Lhs,rule_pos))) ;
 index_term_and_subterms ~is_spine:false rhs
  (fun where -> (Xhs(get_inside where,Rhs,rule_pos)))

let index_sym sym =
 let qname = name_of_sym sym in
 (* Name *)
 DB.insert_name (snd qname) (Name (qname,sym.sym_decl_pos)) ;
 (* Type + InType *)
 let typ = Timed.(!(sym.Core.Term.sym_type)) in
 index_term_and_subterms ~is_spine:true typ
  (fun where -> (Type (where,qname,sym.sym_decl_pos))) ;
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

let locate_cmd_gen ~fail ~pp_results s =
  try
   let qid = Parsing.Parser.Lp.parse_qid s in
   match qid with
    | [],name ->
       let items = locate_name name in
       Format.asprintf "%a@." pp_results items
   | _ ->
       fail (Format.asprintf
        "Syntax error: an unqualified identifier was expected, found %a.%s"
         Common.Path.pp (fst qid) (snd qid))
  with
   exn ->
     fail (Format.asprintf "%s@." (Printexc.to_string exn))

let locate_cmd_html s =
 locate_cmd_gen ~fail:(fun x -> x) ~pp_results:html_of_item_set s

let locate_cmd_txt s =
 locate_cmd_gen ~fail:(fun x -> Common.Error.fatal_no_pos "%s" x)
  ~pp_results:pp_item_set s

let search_cmd_gen ~fail ?(holes_in_index=false) ~pp_results s =
  try
   let ptermstream = Parsing.Parser.Lp.parse_term_string "LPSearch" s in
   let pterm = Stream.next ptermstream in
   let mok _ = None in
   let items = search_pterm ~holes_in_index ~mok [] pterm in
   Format.asprintf "%a@." pp_results items
  with
   | Stream.Failure ->
      fail (Format.asprintf "Syntax error: a term was expected")
   | exn ->
      fail (Format.asprintf "%s@." (Printexc.to_string exn))

let search_cmd_html ?holes_in_index s =
 search_cmd_gen ~fail:(fun x -> x) ~pp_results:html_of_item_set
  ?holes_in_index s

let search_cmd_txt ?holes_in_index s =
 search_cmd_gen ~fail:(fun x -> Common.Error.fatal_no_pos "%s" x)
 ~pp_results:pp_item_set ?holes_in_index s
