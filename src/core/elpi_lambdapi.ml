open Elpi.API

module Elpi_AUX = struct
  let array_map_fold f st a =
    let len = Array.length a in
    let st = ref st in
    let b = Array.make len RawData.mkNil in
    for i = 0 to len-1 do
      let st', x = f !st a.(i) in
      st := st';
      b.(i) <- x
    done;
    !st, b

  let list_map_fold f s l =
    let f st x = let st, x = f st x in st, x, [] in
    let s, l, _ = Utils.map_acc f s l in
    s, l

  let loc_of_pos = function
    | None -> Ast.Loc.initial "(elpi)"
    | Some x ->
        let { Common.Pos.fname; start_line; start_col; _ } = x in
        {
          Ast.Loc.source_name =
            (match fname with None -> "(.)" | Some x -> x);
          source_start = 0;
          source_stop = 0;
          line = start_line;
          line_starts_at = start_col;
        }

end

(** Terms.sym is exposed to Elpi as an opaque data type (no syntax like int or
    string). APIs are provided to manipulate symbols, eg get their type *)
let sym : Term.sym Conversion.t = OpaqueData.declare {
  OpaqueData.name = "symbol";
  doc = "A symbol";
  pp = Print.sym;
  compare = Term.Sym.compare;
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [];
}

(** Waiting for a ppx to do all the work for us, we code by hand the
    conversion of Terms.term *)

(* Allocate Elpi symbols for the term constructors (type and kind are Elpi
   keywords, hence typ and kin) *)
let typec = RawData.Constants.declare_global_symbol "typ"
let kindc = RawData.Constants.declare_global_symbol "kin"
let symbc = RawData.Constants.declare_global_symbol "symb"
let prodc = RawData.Constants.declare_global_symbol "prod"
let abstc = RawData.Constants.declare_global_symbol "abst"
let applc = RawData.Constants.declare_global_symbol "appl"

(* A two way map linking Elpi's unification variable and Terms.meta.
   An instance of this map is part of the Elpi state (threaded by many
   APIs) *)
module M = struct
  type t = Term.meta
  let compare m1 m2 = Stdlib.compare m1.Term.meta_key m2.Term.meta_key
  let pp = Print.meta
  let show m = Format.asprintf "%a" pp m
end
module MM = FlexibleData.Map(M)
let metamap : MM.t State.component = MM.uvmap

let pb = State.declare ~name:"elpi:problem"
  ~pp:(fun fmt (p : Term.problem) ->
     Format.fprintf fmt "@[<hov 2>";
     Term.MetaSet.iter (fun m ->
       Format.fprintf fmt "%d@ " m.Term.meta_key) Timed.(! p).Term.metas;
     Format.fprintf fmt "@]";
  ) ~init:Term.new_problem ~start:(fun x -> x)


(* Terms.term -> Data.term, we use Ctxt.ctxt to carry a link between
   Bindlib's var to Elpi's De Bruijn levels *)
let embed_term : ?pats:(int * string) list -> ?ctx:RawData.constant Term.actxt -> Term.term Conversion.embedding = fun ?(pats=[]) ?(ctx=[]) ~depth st t ->
  let open RawData in
  let open Term in
  let gls = ref [] in
  let call f ~depth s x =
    let s, x, g = f ~depth s x in gls := g @ !gls; s, x in
  let rec aux ~depth ctx st t =
    match Term.unfold t with
    | Vari v ->
        let d = Ctxt.type_of v ctx in
        st, mkBound d
    | Type -> st, mkGlobal typec
    | Kind -> st, mkGlobal kindc
    | Symb s ->
        let st, s = call sym.Conversion.embed ~depth st s in
        st, mkApp symbc s []
    | Prod (src, tgt) ->
        let st, src = aux ~depth ctx st src in
        let _,tgt,ctx = Ctxt.unbind ctx depth None tgt in
        let st, tgt = aux ~depth:(depth+1) ctx st tgt in
        st, mkApp prodc src [mkLam tgt]
    | Abst (ty, body) ->
        let st, ty = aux ~depth ctx st ty in
        let _,body,ctx = Ctxt.unbind ctx depth None body in
        let st, body = aux ~depth:(depth+1) ctx st body in
        st, mkApp prodc ty [mkLam body]
    | Appl (hd, arg) ->
        let st, hd = aux ~depth ctx st hd in
        let st, arg = aux ~depth ctx st arg in
        st, mkApp applc hd [arg]
    | Meta (meta,args) ->
        let st, flex =
          try st, MM.elpi meta (State.get metamap st)
          with Not_found ->
            let st, flex = FlexibleData.Elpi.make st in
            State.update metamap st (MM.add flex meta), flex in
        let st, args = Elpi_AUX.array_map_fold (aux ~depth ctx) st args in
        st, mkUnifVar flex ~args:(Array.to_list args) st
    | Plac _ ->
        let args = List.map (fun (_,x,_) -> mkBound x) ctx in
        let st, flex = FlexibleData.Elpi.make st in
        let st, meta = State.update_return pb st (fun pb ->
          let m1 = LibMeta.fresh pb mk_Type 0 in
          let m2 = LibMeta.fresh pb (mk_Meta (m1,[||]))
            (List.length args) in (* empty context is surely wrong *)
          pb, m2) in
        let st = State.update metamap st (MM.add flex meta) in
        st, mkUnifVar flex ~args st
    | Patt(Some i,_,_) -> begin
        try
          let x = List.assoc i pats in
          let st, flex = FlexibleData.Elpi.make ~name:x st in
          st, mkUnifVar flex ~args:[] st
        with Not_found ->
          let pats = List.map (fun (i,n) -> Printf.sprintf "%d :-> %s; " i n) pats in
          Common.Error.fatal_no_pos "embed_term: unnamed pattern %d in map: %s" i (String.concat "" pats);
      end
    | Patt _ -> Common.Error.fatal_no_pos "embed_term: Patt not implemented"
    | TEnv _ -> Common.Error.fatal_no_pos "embed_term: TEnv not implemented"
    | Wild   -> Common.Error.fatal_no_pos "embed_term: Wild not implemented"
    | TRef _ -> Common.Error.fatal_no_pos "embed_term: TRef not implemented"
    | LLet _ -> Common.Error.fatal_no_pos "embed_term: LLet not implemented"
  in
  let st, t = aux ~depth ctx st t in
  st, t, List.rev !gls

module IntMap = Map.Make(struct type t = int let compare = compare end)

(* Data.term -> Terms.term. We use and IntMap to link Elpi's De Bruijn
   levels to Bindlib's var *)
let readback_term_box : Term.term Bindlib.box Conversion.readback =
fun ~depth st t ->
  let open RawData in
  let open Term in
  let gls = ref [] in
  let call f ~depth s x =
    let s, x, g = f ~depth s x in gls := g @ !gls; s, x in
  let rec aux ~depth ctx st t =
    match look ~depth t with
    | Const c when c == typec -> st, _Type
    | Const c when c == kindc -> st, _Kind
    | Const c when c >= 0 ->
        begin try
          let v = IntMap.find c ctx in
          st, _Vari v
        with Not_found -> Utils.type_error "readback_term: free variable" end
    | App(c,s,[]) when c == symbc ->
        let st, s = call sym.Conversion.readback ~depth st s in
        st, _Symb s
    | App(c,ty,[bo]) when c == prodc ->
        let st, ty = aux ~depth ctx st ty in
        let st, bo = aux_lam ~depth ctx st bo in
        st, _Prod ty bo
    | App(c,ty,[bo]) when c == abstc ->
        let st, ty = aux ~depth ctx st ty in
        let st, bo = aux_lam ~depth ctx st bo in
        st, _Abst ty bo
    | App(c,hd,[arg]) when c == applc ->
        let st, hd = aux ~depth ctx st hd in
        let st, arg = aux ~depth ctx st arg in
        st, _Appl hd arg
    | UnifVar(flex, args) ->
        let st, meta =
          try st, MM.host flex (State.get metamap st)
          with Not_found ->
            let st, m2 = State.update_return pb st (fun pb ->
              let m1 = LibMeta.fresh pb mk_Type 0 in
              let m2 = LibMeta.fresh pb (mk_Meta (m1,[||]))
                (List.length args) in (* empty context is surely wrong *)
              pb, m2) in
            State.update metamap st (MM.add flex m2), m2
           in
        let st, args = Elpi_AUX.list_map_fold (aux ~depth ctx) st args in
        st, _Meta meta (Array.of_list args)
    | _ -> Utils.type_error "readback_term"
  and aux_lam ~depth ctx st t =
    match look ~depth t with
    | Lam bo ->
        let v = Bindlib.new_var of_tvar "x" in
        let ctx = IntMap.add depth v ctx in
        let st, bo = aux ~depth:(depth+1) ctx st bo in
        st, Bindlib.bind_var v bo
    | _ -> Utils.type_error "readback_term"
  in
  let st, t = aux ~depth IntMap.empty st t in
  st, t, List.rev !gls

let readback_term ~depth st t =
  let st, t, gls = readback_term_box ~depth st t in
  st, Bindlib.unbox t, gls

(** Terms.term has a HOAS *)
let term : Term.term Conversion.t = {
  Conversion.ty = Conversion.TyName "term";
  pp = Print.term;
  pp_doc = (fun fmt () -> Format.fprintf fmt {|
kind term type.
type typ term.
type kin term.
type symb symbol -> term.
type appl term -> term -> term.
type abst term -> (term -> term) -> term.
type prod term -> (term -> term) -> term.
  |});
  readback = readback_term;
  embed = embed_term ?ctx:None ?pats:None;
}

(** Assignments to Elpi's unification variables are a spine of lambdas
    followed by an actual term. We read them back as a Bindlib.mbinder *)
let readback_mbinder st t =
  let open RawData in
  let rec aux ~depth nvars t =
    match look ~depth t with
    | Lam bo -> aux ~depth:(depth+1) (nvars+1) bo
    | _ ->
        let open Bindlib in
        let vs = Array.init nvars (fun i ->
          new_var Term.of_tvar (Printf.sprintf "x%d" i)) in
        let st, t, _ = readback_term_box ~depth st t in
        st, unbox (bind_mvar vs t)
  in
    aux ~depth:0 0 t
let readback_assignments st =
  let mmap = State.get metamap st in
  MM.fold (fun meta _flex body st ->
    match body with
    | None -> st
    | Some t ->
        let open Timed in
        match ! (meta.Term.meta_value) with
        | Some _ -> assert false
        | None ->
            let st, t = readback_mbinder st t in
            meta.Term.meta_value := Some t;
            st
    ) mmap st

