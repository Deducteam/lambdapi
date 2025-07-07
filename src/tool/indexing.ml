open Core open Term
open Common open Pos

type sym_name = Common.Path.t * string

let string_of_path x = Format.asprintf "%a" Common.Path.pp x

let is_path_prefix patt p =
 Lplib.String.is_prefix patt (string_of_path p)

let re_matches_sym_name re (p,name) =
 try
  ignore (Str.search_forward re (string_of_path p ^ "." ^ name) 0) ;
  true
 with Not_found -> false

let name_of_sym s = (s.sym_path, s.sym_name)

(* Tail recursive implementation of List.append for
   OCaml < 5.1 *)
let (@) l1 l2 = List.rev_append (List.rev l1) l2

let dump_to ~filename i =
 let ch = open_out_bin filename in
 Marshal.to_channel ch i [] ;
 close_out ch

let restore_from ~filename =
  let ch = open_in_bin filename in
  let i = Marshal.from_channel ch in
  close_in ch ;
  i

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

module Index = struct

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

let rec node_of_stack t s v =
 match unfold t with
 | Kind -> IRigid(IKind, index_of_stack s v)
 | Type -> IRigid(IType, index_of_stack s v)
 | Vari _ -> IRigid(IVar, index_of_stack s v)
 | Symb sym  -> IRigid(ISymb (name_of_sym sym), index_of_stack s v)
 | Appl(t1,t2) -> IRigid(IAppl, index_of_stack (t1::t2::s) v)
 | Abst(t1,bind) ->
    let _, t2 = unbind bind in
    IRigid(IAbst, index_of_stack (t1::t2::s) v)
 | Prod(t1,bind) ->
    let _, t2 = unbind bind in
    IRigid(IProd, index_of_stack (t1::t2::s) v)
 | Patt (_var,_varname,_args) ->
    IHOLE (index_of_stack s v)
 | LLet (_typ, bod, bind) ->
    (* Let-ins are expanded during indexing *)
    node_of_stack (subst bind bod) s v
 | Meta _ -> assert false
 | Plac _ -> assert false (* not for meta-closed terms *)
 | Wild -> assert false (* used only by tactics and reduction *)
 | TRef _  -> assert false (* destroyed by unfold *)
 | Bvar _ -> assert false

and index_of_stack stack v =
 match stack with
 | [] -> Leaf [v]
 | t::s -> Choice [node_of_stack t s v]

exception NoMatch

(* match a rigid with a term, either raising NoMatch or returning the
   (ordered) list of immediate subterms of the term *)
let rec match_rigid r term =
 match r, unfold term with
 | IKind, Kind -> []
 | IType, Type -> []
 | IVar, Vari _ -> []
 | ISymb n, Symb sym  when n = name_of_sym sym -> []
 | IAppl, Appl(t1,t2) -> [t1;t2]
 | IAbst, Abst(t1,bind) -> let _, t2 = unbind bind in [t1;t2]
 | IProd, Prod(t1,bind) -> let _, t2 = unbind bind in [t1;t2]
 | _, LLet (_typ, bod, bind) -> match_rigid r (subst bind bod)
 | _, (Meta _ | Plac _ | Wild | TRef _) -> assert false
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

let rec remove_index ~what =
 function
  | Leaf l ->
     let l' = List.filter what l in
     (match l' with
       | [] -> Choice []
       | _::_ -> Leaf l')
  | Choice l ->
     Choice (List.filter_map (remove_node ~what) l)

and remove_node ~what =
 function
  | IHOLE i ->
     (match remove_index ~what i with
       | Choice [] -> None
       | i' -> Some (IHOLE i'))
  | IRigid (r,i) ->
     (match remove_index ~what i with
       | Choice [] -> None
       | i' -> Some (IRigid (r,i')))

let remove_from_name_index ~what i =
 Lplib.Extra.StrMap.filter_map
  (fun _ l ->
    let f x = if what x then Some x else None in
    match List.filter_map f l with
     | [] -> None
     | l' -> Some l') i

let remove ~what (dbname, index) =
 remove_from_name_index ~what dbname, remove_index ~what index

let rec search_index ~generalize index stack =
 match index,stack with
 | Leaf vs, [] -> vs
 | Choice l, t::s ->
    List.fold_right
     (fun n res -> search_node ~generalize n t s @ res) l []
 | _, _ -> assert false (* ill-typed term *)

and search_node ~generalize node term s =
 match node,term with
 | _, Patt _ ->
     List.concat
      (List.map
        (fun i -> search_index ~generalize i s) (match_flexible node))
 | IHOLE i, _ when generalize -> search_index ~generalize i s
 | IHOLE i, t -> search_node ~generalize (IRigid(IVar,i)) t s
 | IRigid(r,i), t ->
     match match_rigid r t with
     | s' -> search_index ~generalize i (s'@s)
     | exception NoMatch -> []

(* when [~generalize] is false, all holes in the index are matched
   only by variables, i.e. the pattern is not matched up to generalization *)
let search ~generalize (_,index) term =
 search_index ~generalize index [term]

let locate_name (namemap,_) name =
  match Lplib.Extra.StrMap.find_opt name namemap with None -> [] | Some l -> l

end

module DB = struct
 (* fix codomain type *)

 type side = Parsing.SearchQuerySyntax.side = Lhs | Rhs

 type inside = Parsing.SearchQuerySyntax.inside = Exact | Inside

 type 'inside where = 'inside Parsing.SearchQuerySyntax.where =
  | Spine of 'inside
  | Conclusion of 'inside
  | Hypothesis of 'inside
 (* the "name" in the sym_name of rules is just the printed position of
    the rule; the associated position is never None *)

 type position =
  | Name
  | Type of inside where
  | Xhs  of inside * side

 type item = sym_name * Common.Pos.pos option

 let pp_side fmt =
  function
   | Lhs -> Lplib.Base.out fmt "lhs"
   | Rhs -> Lplib.Base.out fmt "rhs"

 let pp_inside fmt =
  function
    | Exact -> Lplib.Base.out fmt "as the exact"
    | Inside -> Lplib.Base.out fmt "inside the"

 let pp_where fmt =
  function
   | Spine ins -> Lplib.Base.out fmt "%a spine of" pp_inside ins
   | Hypothesis ins -> Lplib.Base.out fmt "%a hypothesis of" pp_inside ins
   | Conclusion ins -> Lplib.Base.out fmt "%a conclusion of" pp_inside ins

 module ItemSet =
  struct
   include Map.Make(struct type t = item let compare = compare end)

   let of_list l =
    List.fold_left
     (fun m (k,v) ->
       update k
        (function
          | None -> Some v
          | Some l -> Some (v@l))
        m) empty l
  end

 module Sym_nameMap =
   Map.Make(struct type t = sym_name let compare = compare end)

 type answer = ((*generalized:*)bool * term * position) list

 (* disk persistence *)

 let the_dbpath : string ref = ref Path.default_dbpath

 let rwpaths = ref []

 let restore_from_disk () =
  try restore_from ~filename:!the_dbpath
  with Sys_error msg ->
     Common.Error.wrn None "%s.\n\
      Type \"lambdapi index --help\" to learn how to create the index." msg ;
     Sym_nameMap.empty, Index.empty

 (* The persistent database *)
 let db :
  ((string * string * int * int) Sym_nameMap.t *
   (item * position list) Index.db) Lazy.t ref =
   ref (lazy (restore_from_disk ()))

 let empty () = db := lazy (Sym_nameMap.empty,Index.empty)

 let insert k v =
   let sidx,idx = Lazy.force !db in
   let db' = sidx, Index.insert idx k v in
   db := lazy db'

 let insert_name k v =
   let sidx,idx = Lazy.force !db in
   let db' = sidx, Index.insert_name idx k v in
   db := lazy db'

 let remove path =
   let sidx,idx = Lazy.force !db in
   let keep sym_path = not (is_path_prefix path sym_path) in
   let idx =
     Index.remove
      ~what:(fun (((sym_path,_),_),_) -> keep sym_path ) idx in
   let sidx =
    Sym_nameMap.filter (fun (sym_path,_) _ -> keep sym_path) sidx in
   db := lazy (sidx,idx)

 let set_of_list ~generalize k l =
  (* rev_map is used because it is tail recursive *)
  ItemSet.of_list
   (List.rev_map
     (fun (i,pos) ->
       i, List.map (fun x -> generalize,k,x) pos) l)

 let search ~generalize k =
  set_of_list ~generalize k
   (Index.search ~generalize (snd (Lazy.force !db)) k)

 let dump ~dbpath () =
  dump_to ~filename:dbpath (Lazy.force !db)

 let locate_name name =
  let k = Term.mk_Wild (* dummy, unused *) in
  set_of_list ~generalize:false k
   (Index.locate_name (snd (Lazy.force !db)) name)

 let parse_source_map filename =
  let sidx,idx = Lazy.force !db in
  let sidx = ref sidx in
  let ch = open_in filename in
  (try
   while true do
     let line = input_line ch in
     match String.split_on_char ' ' line with
      | [fname; start_line; end_line; sourceid; lpid] ->
          let rec sym_name_of =
           function
             | [] -> assert false
             | [name] -> [],name
             | hd::tl -> let path,name = sym_name_of tl in hd::path,name in
          let lpid = sym_name_of (String.split_on_char '.' lpid) in
          let start_line = int_of_string start_line in
          let end_line = int_of_string end_line in
          sidx :=
           Sym_nameMap.add lpid (sourceid,fname,start_line,end_line) !sidx
      | _ ->
         raise
          (Common.Error.Fatal(None,"wrong file format for source map file"))
   done ;
  with
   | Failure _ as exn ->
      close_in ch;
      raise
       (Common.Error.Fatal(None,"wrong file format for source map file: " ^
         Printexc.to_string exn))
   | End_of_file -> close_in ch) ;
  db := lazy (!sidx,idx)


 type ho_pp = { run : 'a. 'a Lplib.Base.pp -> 'a Lplib.Base.pp }

 let identity_escaper : ho_pp =
  { run = fun x -> x }

 let html_escaper : ho_pp =
  { run  = fun pp fmt x ->
     let res = Dream.html_escape (Format.asprintf "%a" pp x) in
     Format.pp_print_string fmt res
  }

 let source_infos_of_sym_name sym_name =
  match Sym_nameMap.find_opt sym_name (fst (Lazy.force !db)) with
   | None -> None, None
   | Some (sourceid, fname, start_line, end_line) ->
      let start_col = 0 in
      let end_col = -1 in (* to the end of line *)
      Some sourceid,
       Some { fname=Some fname; start_line; start_col; end_line; end_col }

 let generic_pp_of_position_list ~escaper ~sep =
  Lplib.List.pp
   (fun ppf position ->
     Print.no_qualif (fun () ->
     match position with
      | _,_,Name ->
         Lplib.Base.out ppf "Name"
      | generalize,term,Type where ->
         Lplib.Base.out ppf "%a occurs %s%a the type"
          (escaper.run Print.term) term
          (if generalize then "generalized " else "")
          pp_where where
      | generalize,term,Xhs (inside,side) ->
         Lplib.Base.out ppf "%a occurs %s %a %a"
          (escaper.run Print.term) term
          (if generalize then "generalized" else "")
          pp_inside inside pp_side side))
   sep

 let generic_pp_of_item_list ~escape ~escaper ~separator ~sep ~delimiters
  ~lis:(lisb,lise) ~pres:(preb,pree)
  ~bold:(boldb,bolde) ~code:(codeb,codee) fmt l
 =
  if l = [] then
   Lplib.Base.out fmt "Nothing found"
  else
   Lplib.List.pp
    (fun ppf (((p,n) as sym_name,pos),(positions : answer)) ->
     let sourceid,sourcepos = source_infos_of_sym_name sym_name in
     Lplib.Base.out ppf "%s%a.%s%s%s@%s%s%a%s%s%s%a%s%a%s%a%s%s%s@."
       lisb (escaper.run Core.Print.path) p boldb n bolde
       (popt_to_string ~print_dirname:false pos)
       separator (generic_pp_of_position_list ~escaper ~sep) positions
       separator preb codeb
       (Common.Pos.print_file_contents ~escape ~delimiters
         ~complain_if_location_unknown:true) pos
       separator
       (fun ppf opt ->
         match opt with
          | None -> Lplib.Base.string ppf ""
          | Some sourceid ->
             Lplib.Base.string ppf ("Translated to " ^ sourceid)) sourceid
       separator
       (Common.Pos.print_file_contents ~escape ~delimiters
         ~complain_if_location_unknown:false) sourcepos
       codee pree lise)
    "" fmt l

 let html_of_item_list =
  generic_pp_of_item_list ~escape:Dream.html_escape ~escaper:html_escaper
   ~separator:"<br>\n" ~sep:" and<br>\n" ~delimiters:("<p>","</p>")
   ~lis:("<li>","</li>") ~pres:("<pre>","</pre>") ~bold:("<b>","</b>")
   ~code:("<code>","</code>")

 let pp_item_list =
  generic_pp_of_item_list ~escape:(fun x -> x) ~escaper:identity_escaper
   ~separator:"\n" ~sep:" and\n" ~delimiters:("","")
   ~lis:("* ","") ~pres:("","") ~bold:("","") ~code:("","")

 let pp_results_list fmt l = pp_item_list fmt l

 let html_of_results_list from fmt l =
  Lplib.Base.out fmt "<ol start=\"%d\">%a</ol>" from html_of_item_list l

end

exception Overloaded of string * DB.answer DB.ItemSet.t

let find_sym ~prt ~prv sig_state ({elt=(mp,name); pos} as s) =
 let pos,mp =
  match mp with
    [] ->
     let res = DB.locate_name name in
     if DB.ItemSet.cardinal res > 1 then
       raise (Overloaded (name,res)) ;
     (match DB.ItemSet.choose_opt res with
       | None -> Common.Error.fatal pos "Unknown symbol %s." name
       | Some (((mp,_),sympos),[_,_,DB.Name]) -> sympos,mp
       | Some _ -> assert false) (* locate only returns DB.Name*)
  | _::_ -> None,mp
 in
 try
  Core.Sig_state.find_sym ~prt ~prv sig_state s
 with
  Common.Error.Fatal _ ->
   Core.Term.create_sym mp Core.Term.Public Core.Term.Defin Core.Term.Sequen
    false (Common.Pos.make pos name) None Core.Term.mk_Type []

module QNameMap =
 Map.Make(struct type t = sym_name let compare = Stdlib.compare end)

let no_implicits_in_term t =
 let res = ref true in
 Core.LibTerm.iter
  (function
    | Plac _ -> res := false
    | Wild | TRef _ -> assert false
    | _ -> ()) t ;
 !res

let check_rule : Parsing.Syntax.p_rule -> sym_rule = fun pr ->
 let ss = Core.Sig_state.dummy in
 let (_,r) as sr = Parsing.Scope.scope_rule ~find_sym false ss pr in
 if no_implicits_in_term r.rhs then sr
 else
  Common.Error.fatal pr.pos
   "The rule has implicit terms in the right-hand-side: %a"
   (Parsing.Pretty.rule "") pr

let load_meta_rules () =
 let rules = ref [] in
 List.iter (fun rwpath ->
  let cmdstream = Parsing.Parser.Lp.parse_file rwpath in
  Stream.iter
   (fun {elt ; _ } ->
     match elt with
       Parsing.Syntax.P_rules r -> rules := List.rev_append r !rules
     | _ -> ())
   cmdstream) !DB.rwpaths ;
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
  try QNameMap.find (name_of_sym sym) (Lazy.force meta_rules)
  with Not_found -> Core.Tree_type.empty_dtree in
 Core.Eval.snf ~dtree ~tags:[`NoExpand] [] typ

let search_pterm ~generalize ~mok ss env pterm =
 let env =
  ("V#",(new_var "V#",Term.mk_Type,None))::env in
 let query =
  Parsing.Scope.scope_search_pattern ~find_sym ~mok ss env pterm in
 Dream.log "QUERY before: %a" Core.Print.term query ;
 let query = normalize query in
 Dream.log "QUERY after: %a" Core.Print.term query ;
 DB.search ~generalize query

let rec is_flexible t =
 match Core.Term.unfold t with
  | Patt _ -> true
  | Appl(t,_) -> is_flexible t
  | LLet(_,_,b) -> let _, t = unbind b in is_flexible t
  | Vari _ | Type | Kind | Symb _ | Prod _ | Abst _ -> false
  | Meta _ | Plac _ | Wild | TRef _ | Bvar _ -> assert false

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
  | Bvar _
  | Vari _
  | Type
  | Kind
  | Symb _ -> []
  | Abst(t,b) ->
     let _, t2 = unbind b in
     aux ~where:(enter where) t @ aux ~where:(enter where) t2
  | Prod(t,b) ->
     (match where with
       | Spine _ ->
          let t2 = subst b (Core.Term.mk_Patt (None,"dummy",[||])) in
          aux ~where:(enter_pi_source where) t @
           aux ~where:(enter_pi_target ~is_prod:(Core.Term.is_prod t2) where)
            t2
       | _ ->
         let _, t2 = unbind b in
         aux ~where:(enter_pi_source where) t @
          aux ~where:(enter_pi_target ~is_prod:false where) t2)
  | Appl(t1,t2) ->
     aux ~where:(enter where) t1 @ aux ~where:(enter where) t2
  | Patt (_var,_varname,args) ->
     List.concat (List.map (aux ~where:(enter where)) (Array.to_list args))
  | LLet (t1,t2,b) ->
     (* we do not expand the let-in when indexing subterms *)
     let _, t3 = unbind b in
     aux ~where:(enter where) t1 @ aux ~where:(enter where) t2 @
      aux ~where:(enter where) t3
  | Meta _ | Plac _ | Wild | TRef _ -> assert false
 in aux ~where:(if is_spine then Spine Exact else Conclusion Exact) t

let insert_rigid t v =
 if not (is_flexible t) then begin
  DB.insert t v
  (* assert (List.mem v (DB.search t)); *)
 end

let index_term_and_subterms ~is_spine t item =
 let tn = normalize t in
 (*
 let pp_item ppf (((p,n),_ ), _) =
   Lplib.Base.out ppf "%a.%s" Core.Print.path p n in
 Format.printf "%a :(%a) REWRITTEN TO (%a)@."
  pp_item (item (DB.Conclusion DB.Exact))
  Core.Print.term t Core.Print.term tn ;
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
 let rhs = rule.rhs in
 let get_inside = function | DB.Conclusion ins -> ins | _ -> assert false in
 let filename = Option.get rule_pos.fname in
 let path = Library.path_of_file Parsing.LpLexer.escape filename in
 let rule_name = (path,Common.Pos.to_string ~print_fname:false rule_pos) in
 index_term_and_subterms ~is_spine:false lhs
  (fun where -> ((rule_name,Some rule_pos),[Xhs(get_inside where,Lhs)])) ;
 index_term_and_subterms ~is_spine:false rhs
  (fun where -> ((rule_name,Some rule_pos),[Xhs(get_inside where,Rhs)]))

let index_sym sym =
 let qname = name_of_sym sym in
 (* Name *)
 DB.insert_name (snd qname) ((qname,sym.sym_decl_pos),[Name]) ;
 (* Type + InType *)
 let typ = Timed.(!(sym.Core.Term.sym_type)) in
 index_term_and_subterms ~is_spine:true typ
  (fun where -> ((qname,sym.sym_decl_pos),[Type where])) ;
 (* InBody??? sym.sym_def : term option ref
    but all the subterms are too much; collect only the constants? *)
 (* Rules *)
 List.iter (index_rule sym) Timed.(!(sym.Core.Term.sym_rules))

let load_rewriting_rules rwrules =
 DB.rwpaths := rwrules

let index_sign sign =
 (*Console.set_flag "print_domains" true ;
 Console.set_flag "print_implicits" true ;
 Common.Logger.set_debug true "e" ;*)
 let syms = Timed.(!(sign.Core.Sign.sign_symbols)) in
 let rules = Timed.(!(sign.Core.Sign.sign_deps)) in
 Lplib.Extra.StrMap.iter (fun _ sym -> index_sym sym) syms ;
 Common.Path.Map.iter
  (fun path rules ->
    Lplib.Extra.StrMap.iter
     (fun name (rules,_) ->
       let sym = Core.Sign.find_sym path name in
       List.iter (index_rule sym) rules)
     rules)
  rules

let deindex_path path = DB.remove path

(* let's flatten the interface *)
include DB

module QueryLanguage = struct

 open Parsing.SearchQuerySyntax

 let match_opt p x =
  match p,x with
  | None, _ -> true
  | Some x', x -> x=x'

 let match_where p x =
  match p with
  | None -> true
  | Some p ->
     match p,x with
      | Spine insp, Spine ins
      | Conclusion insp, Conclusion ins
      | Hypothesis insp, Hypothesis ins -> match_opt insp ins
      | _, _ -> false

 let filter_constr constr _ positions =
  Option.map (fun x -> [x])
   (match constr with
    | QType wherep ->
       List.find_opt
        (function
          | _,_,Type where -> match_where wherep where
          | _ -> false) positions
    | QXhs (insp,sidep) ->
       List.find_opt
        (function
          | _,_,Xhs (ins,side) -> match_opt insp ins && match_opt sidep side
          | _ -> false) positions)

 let answer_base_query ~mok ss env =
  function
   | QName s -> locate_name s
   | QSearch (patt,generalize,constr) ->
      let res = search_pterm ~generalize ~mok ss env patt in
      (match constr with
        | None -> res
        | Some constr -> ItemSet.filter_map (filter_constr constr) res)

 let perform_op =
  function
   | Intersect ->
       ItemSet.merge
        (fun _ positions1 positions2 ->
          match positions1, positions2 with
           | Some l1, Some l2 -> Some (l1@l2)
           | _,_ -> None)
   | Union ->
       ItemSet.union
        (fun _ positions1 positions2 -> Some (positions1 @ positions2))

 let filter set f =
  let g ((p',_ as name),_) _ =
   match f with
    | Path p -> is_path_prefix p p'
    | RegExp re -> re_matches_sym_name re name in
  ItemSet.filter g set

 let answer_query ~mok ss env =
  let rec aux =
   function
    | QBase bq -> answer_base_query ~mok ss env bq
    | QOpp (q1,op,q2) -> perform_op op (aux q1) (aux q2)
    | QFilter (q,f) -> filter (aux q) f
  in
   aux

end

(* let's flatten the interface *)
include QueryLanguage

module UserLevelQueries = struct

  (**transform_ascii_to_unicode [s] replaces all the occurences of '->'
    and 'forall' with '→' and 'Π' in the search query [s] *)
  let transform_ascii_to_unicode : string -> string = fun s ->
    let s = Str.global_replace (Str.regexp_string " -> ") " → " s in
    Str.global_replace (Str.regexp "\\bforall\\b") "Π" s

 let search_cmd_gen ss ~from ~how_many ~fail ~pp_results
  ~title_tag:(hb,he) s =
  let s = transform_ascii_to_unicode s in
  try
   let pstream = Parsing.Parser.Lp.parse_search_query_string "LPSearch" s in
   let pq = Stream.next pstream in
   let mok _ = None in
   let items = ItemSet.bindings (answer_query ~mok ss [] pq) in
   let resultsno = List.length items in
   let _,items = Lplib.List.cut items from in
   let items,_ = Lplib.List.cut items how_many in
   Format.asprintf "%sNumber of results: %d%s%a@."
    hb resultsno he pp_results items
  with
   | Stream.Failure ->
      fail (Format.asprintf "Syntax error: a query was expected")
   | Common.Error.Fatal(_,msg) ->
      fail (Format.asprintf "Error: %s@." msg)
   | Overloaded(name,res) ->
      fail (Format.asprintf
       "Overloaded symbol %s. Please rewrite the query replacing %s \
        with a fully qualified identifier among the following: %a"
        name name pp_results (ItemSet.bindings res))
   | Stack_overflow ->
      fail
       (Format.asprintf
         "Error: too many results. Please refine your query.@." )
   | exn ->
      fail (Format.asprintf "Error: %s@." (Printexc.to_string exn))

 let search_cmd_html ss ~from ~how_many s ~dbpath =
  the_dbpath := dbpath;
  search_cmd_gen ss ~from ~how_many
   ~fail:(fun x -> "<font color=\"red\">" ^ x ^ "</font>")
   ~pp_results:(html_of_results_list from) ~title_tag:("<h1>","</h1>") s

 let search_cmd_txt ss s ~dbpath =
  the_dbpath := dbpath;
  search_cmd_gen ss ~from:0 ~how_many:999999
   ~fail:(fun x -> Common.Error.fatal_no_pos "%s" x)
   ~pp_results:pp_results_list ~title_tag:("","") s

end

(* let's flatten the interface *)
include UserLevelQueries

let _ =
  assert (transform_ascii_to_unicode "a -> b" = "a → b");
  assert (transform_ascii_to_unicode " forall x, y" = " Π x, y");
  assert (transform_ascii_to_unicode "forall x, y" = "Π x, y");
  assert (transform_ascii_to_unicode "forall.x, y" = "Π.x, y");
  assert (transform_ascii_to_unicode "((forall x, y" = "((Π x, y")
