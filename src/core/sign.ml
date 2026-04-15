(** Signature for symbols. *)

open Lplib open Extra
open Common open Pos
open Timed
open Term
module J = Yojson.Basic

(** Data associated to inductive types. *)
type ind_data =
  { ind_cons : sym list (** Constructors. *)
        [@to_yojson fun m -> `List (List.map sym_to_yojson m)]
      [@of_yojson fun j ->
        match j with
        |`List l ->
          let rec aux acc l =
            begin match l with
            | [] -> Ok acc
            | el :: lt -> begin match sym_of_yojson el with
            | Ok x -> aux (x :: acc) lt
            | Error e -> Error e
          end
            end
          in
          aux [] l
        |_ -> Error "Expected list of sym_json"
          ]
  ; ind_prop : sym      (** Induction principle. *)
        [@to_yojson fun m ->
          sym_to_yojson m]
      [@of_yojson fun j ->
          sym_of_yojson j]
  ; ind_nb_params : int (** Number of parameters. *)
  ; ind_nb_types : int  (** Number of mutually defined types. *)
  ; ind_nb_cons : int   (** Number of constructors. *) }
  [@@deriving yojson]

type sym_data =
  { rules : rule list
  [@to_yojson fun l ->
         `List (List.map
           (fun r -> rule_serializable_to_yojson (to_rule_serializable r))
           l)]
      [@of_yojson fun j ->
         match j with
         | `List lst ->
             let rec aux acc = function
               | [] -> Ok (List.rev acc)
               | x :: xs ->
                   begin match rule_serializable_of_yojson x with
                   | Ok r_ser ->
                       aux (of_rule_serializable r_ser :: acc) xs
                   | Error e -> Error e
                   end
             in
             aux [] lst
         | _ -> Error "rules: expected list"]
  ; nota : float notation option }[@@deriving yojson]

  let strmap_to_yojson to_elt (m : 'a StrMap.t) : Yojson.Safe.t =
  `List (
    StrMap.bindings m
    |> List.map (fun (k, v) ->
         `List [`String k; to_elt v])
  )

let strmap_of_yojson of_elt (json : Yojson.Safe.t)
  : ('a StrMap.t, string) result =
  match json with
  | `List lst ->
      let rec aux acc = function
        | [] -> Ok acc
        | `List [`String k; v_json] :: tl ->
            begin match of_elt v_json with
            | Ok v -> aux (StrMap.add k v acc) tl
            | Error e -> Error e
            end
        | _ -> Error "StrMap.of_yojson: invalid entry"
      in
      aux StrMap.empty lst
  | _ -> Error "StrMap.of_yojson: expected list"

let pathmap_to_yojson to_elt (m : 'a Path.Map.t) : Yojson.Safe.t =
   `List (
    Path.Map.bindings m
      |> List.map (fun (k, v) ->
        `List [`String (Format.asprintf "%a" Path.Path.pp k); to_elt v]
   ))

let pathmap_of_yojson of_elt json =
  match json with
  | `List lst ->
    let rec aux acc l =
      match l with
      | [] -> Ok acc
      | `List [`String k; v_json] :: lt ->
        begin match of_elt v_json with
        | Ok v ->
          aux (Path.Map.add (Path.Path.make k) v acc) lt
        | Error e -> Error e
        end
      | _ -> Error "pas list"
    in
    aux Path.Map.empty lst
  | _ -> Error "pathmap_of_yojson: expected list"


let symmap_to_yojson to_elt (m : 'a SymMap.t) : Yojson.Safe.t =
  `List (
    SymMap.bindings m
    |> List.map (fun (k, v) ->
         `List [ sym_to_yojson k; to_elt v ])
  )

let symmap_of_yojson of_elt (json : Yojson.Safe.t)
  : ('a SymMap.t, string) result =
  match json with
  | `List lst ->
      let rec aux acc = function
        | [] -> Ok acc
        | `List [k_json; v_json] :: tl ->
            begin match (sym_of_yojson k_json), of_elt v_json with
            | Ok k, Ok v ->
                aux (SymMap.add k v acc) tl
            | Error e, _ -> Error e
            | _, Error e -> Error e
            end
        | _ -> Error "SymMap.of_yojson: invalid entry"
      in
      aux SymMap.empty lst
  | _ -> Error "SymMap.of_yojson: expected list"

(* module Symdata_StrMap_serializable = struct
include StrMap
let strMap_serializable_to_yojson m =
  strmap_to_yojson sym_data_to_yojson m
let strMap_serializable_to_yojson m =
  strmap_of_yojson sym_data_of_yojson m
end *)

(** Data associated to a dependency. *)
type dep_data =
  { dep_symbols : sym_data StrMap.t
      [@to_yojson fun m ->
         strmap_to_yojson sym_data_to_yojson m]
      [@of_yojson fun j ->
         strmap_of_yojson sym_data_of_yojson j]
  ; dep_open : bool }
  [@@deriving yojson]

(** Representation of a signature, that is, what is introduced by a
    module/file. Signatures must be created with the functions [create] or
    [read] below only.*)
(* type t =
  { sign_symbols  : sym StrMap.t ref            (*OK*)
  ; sign_path     : Path.t                      (*OK*)
  ; sign_deps     : dep_data Path.Map.t ref     (*OK*)
  ; sign_builtins : sym StrMap.t ref            (*OK*)
  ; sign_ind      : ind_data SymMap.t ref
  ; sign_cp_pos   : cp_pos list SymMap.t ref
  } *)

  type t =
  { sign_symbols  : sym StrMap.t ref
        [@to_yojson fun m ->
         strmap_to_yojson sym_to_yojson (Timed.(!)m)]
        [@of_yojson fun j ->
         match (strmap_of_yojson sym_of_yojson j) with
          |Ok x -> Ok (Timed.ref x)
          | Error e -> Error e
         ]
  ; sign_path     : Path.t
  ; sign_deps     : dep_data Path.Map.t ref
        [@to_yojson fun m ->
         pathmap_to_yojson dep_data_to_yojson (Timed.(!)m)]
        [@of_yojson fun m ->
          match pathmap_of_yojson dep_data_of_yojson m with
          | Ok x -> Ok (ref x)
          | Error e -> Error e ]
  ; sign_builtins : sym StrMap.t ref
        [@to_yojson fun m ->
         strmap_to_yojson sym_to_yojson !m]
        [@of_yojson fun j ->
         match strmap_of_yojson sym_of_yojson j with
          | Ok x -> Ok (ref x)
          | Error e -> Error e ]
  ; sign_ind      : ind_data SymMap.t ref
        [@to_yojson fun m ->
          symmap_to_yojson ind_data_to_yojson !m
         ]
        [@of_yojson fun json ->
            match symmap_of_yojson
              (ind_data_of_yojson
              ) json with
          | Ok x -> Ok (ref x)
          | Error e -> Error e
          ]
  ; sign_cp_pos   : cp_pos list SymMap.t ref
        [@to_yojson fun m ->
          symmap_to_yojson (fun lst ->
            `List (List.map (fun elt -> cp_pos_to_yojson elt) lst)
            ) !m
         ]
        [@of_yojson fun json ->
            match symmap_of_yojson
              (fun j ->
                match j with
                | `List lst ->
                  let rec aux acc = function
                    | [] -> Ok (List.rev acc)
                    | x :: xs ->
                      (match cp_pos_of_yojson x with
                      | Ok v -> aux (v :: acc) xs
                      | Error e -> Error e)
                  in
                  aux [] lst
                | _ -> Error "Expected list for cp_pos list"
              )
              json with
          | Ok x -> Ok (ref x)
          | Error e -> Error e
          ]
  }
  [@@deriving yojson]


let to_yojson_with_version (t : t) (version : string) : Yojson.Safe.t =
  match to_yojson t with
  | `Assoc fields ->
    `Assoc (("version", `String version) :: fields)
  | _ -> assert false

let of_yojson_with_version json =
  let version =
    json
    |> Yojson.Safe.Util.member "version"
    |> Yojson.Safe.Util.to_string in

  if version <> Version.version then
        raise (Failure
          ("Version " ^ version ^ " found but in lpo file but" ^
          Version.version ^ "expected (current)"));

    match json with
    |`Assoc fields ->
      of_yojson (`Assoc (List.remove_assoc "version" fields))
    |_ -> raise (Failure "Unknown po format.
                Field version missing or corrupted file")

(** [mem sign name] checks whether a symbol named [name] exists in [sign]. *)
let mem : t -> string -> bool = fun sign name ->
  StrMap.mem name !(sign.sign_symbols)

(** [find sign name] finds the symbol named [name] in signature [sign] if it
    exists, and raises the [Not_found] exception otherwise. *)
let find : t -> string -> sym = fun sign name ->
  StrMap.find name !(sign.sign_symbols)

(** [loaded] stores the signatures of the known (already compiled or currently
    being compiled) modules. The current module is stored in [loaded] so that
    the symbols that it contains can be qualified with the name of the
    module. This behavior was inherited from previous versions of Dedukti. *)
let loaded : t Path.Map.t ref = ref Path.Map.empty

(** [find_qualified path name] returns the symbol identified by [path] and
    [name] in the known modules (already compiled or currently being
    compiled) *)
let find_qualified : Path.t -> string -> sym = fun path name ->
 find (Path.Map.find path !loaded) name

(** Signature for symbols introduced by Lambdapi and not the user
    (e.g. unification/coercion rules, strings) and always loaded. *)
module Ghost = struct

  let path = Path.ghost "ghost"

  let sign =
    { sign_symbols = ref StrMap.empty
    ; sign_path = path
    ; sign_deps = ref Path.Map.empty
    ; sign_builtins = ref StrMap.empty
    ; sign_ind = ref SymMap.empty
    ; sign_cp_pos = ref SymMap.empty }

  let _ = loaded := Path.Map.add path sign !loaded

  (** [iter f] iters function [f] on ghost symbols. *)
  let iter : (sym -> unit) -> unit = fun f ->
    StrMap.iter (fun _ s -> f s) !(sign.sign_symbols)

end

(** [create path] creates a new signature with path [path] and the ghost
    module as dependency. *)
let create : Path.t -> t = fun sign_path ->
  let dep = {dep_symbols = StrMap.empty; dep_open=true} in
  let sign_deps = ref (Path.Map.singleton Ghost.path dep) in
  { sign_symbols = ref StrMap.empty
  ; sign_path
  ; sign_deps
  ; sign_builtins = ref StrMap.empty
  ; sign_ind = ref SymMap.empty
  ; sign_cp_pos = ref SymMap.empty }

(** [loading] contains the modules that are being processed. They are stored
   in a stack due to dependencies. Note that the topmost element corresponds
   to the current module. If a module appears twice in the stack, then there
   is a circular dependency. *)
let loading : Path.t list ref = ref []

(** [current_path ()] returns the current signature path. *)
let current_path : unit -> Path.t =
  fun () -> (Path.Map.find (List.hd !loading) !loaded).sign_path

(** [link sign] establishes physical links to the external symbols. *)
let link : t -> unit = fun sign ->
  let link_symb s =
    if s.sym_path = sign.sign_path then s
    else
      try find (Path.Map.find s.sym_path !loaded) s.sym_name
      with Not_found ->
        if s.sym_path = Ghost.path
           && String.is_string_literal s.sym_name then
          begin
            Ghost.sign.sign_symbols :=
              StrMap.add s.sym_name s !(Ghost.sign.sign_symbols);
            s
          end
        else assert false
  in
  let link_term mk_Appl =
    let rec link_term t =
      match unfold t with
      | Type
      | Kind
      | Vari _ -> t
      | Symb s -> mk_Symb(link_symb s)
      | Prod(a,b) -> mk_Prod(link_term a, binder link_term b)
      | Abst(a,b) -> mk_Abst(link_term a, binder link_term b)
      | LLet(a,t,b) -> mk_LLet(link_term a, link_term t, binder link_term b)
      | Appl(a,b)   -> mk_Appl(link_term a, link_term b)
      | Patt(i,n,ts)-> mk_Patt(i, n, Array.map link_term ts)
      | Bvar _ -> assert false
      | Meta _ -> assert false
      | Plac _ -> assert false
      | Wild -> assert false
      | TRef _ -> assert false
    in link_term
  in
  let link_lhs = link_term mk_Appl_not_canonical
  and link_term = link_term mk_Appl in
  let link_rule r =
    let lhs = List.map link_lhs r.lhs in
    let rhs = link_term r.rhs in
    {r with lhs ; rhs}
  in
  let f _ s =
    s.sym_type := link_term !(s.sym_type);
    s.sym_def := Option.map link_term !(s.sym_def);
    s.sym_rules := List.map link_rule !(s.sym_rules);
    Tree.update_dtree s []
  in
  StrMap.iter f !(sign.sign_symbols);
  let f mp {dep_symbols=sm; _} =
    if sm <> Extra.StrMap.empty then
      let sign =
        try Path.Map.find mp !loaded with Not_found -> assert false in
      let g n sd =
        let s = try find sign n with Not_found -> assert false in
        s.sym_rules := !(s.sym_rules) @ List.map link_rule sd.rules;
        Option.iter (fun n -> s.sym_nota := n) sd.nota;
        Tree.update_dtree s []
      in
      StrMap.iter g sm
  in
  Path.Map.iter f !(sign.sign_deps);
  sign.sign_builtins := StrMap.map link_symb !(sign.sign_builtins);
  let link_ind_data i =
    { ind_cons = List.map link_symb i.ind_cons;
      ind_prop = link_symb i.ind_prop; ind_nb_params = i.ind_nb_params;
      ind_nb_types = i.ind_nb_types; ind_nb_cons = i.ind_nb_cons }
  in
  let f s i m = SymMap.add (link_symb s) (link_ind_data i) m in
  sign.sign_ind := SymMap.fold f !(sign.sign_ind) SymMap.empty;
  let link_cp_pos (pos,l,r,p,l_p) =
    pos, link_lhs l, link_term r, p, link_lhs l_p in
  let f s cps m = SymMap.add (link_symb s) (List.map link_cp_pos cps) m in
  sign.sign_cp_pos := SymMap.fold f !(sign.sign_cp_pos) SymMap.empty

let link s = Debug.(record_time Sharing (fun () -> link s))

(** [unlink sign] removes references to external symbols (and thus signatures)
    in the signature [sign]. This function is used to minimize the size of
    object files, by preventing a recursive inclusion of all the dependencies.
    Note however that [unlink] processes [sign] in place, which means that the
    signature is invalidated in the process. *)
let unlink : t -> unit = fun sign ->
  let unlink_sym s =
    s.sym_dtree := Tree_type.empty_dtree;
    if s.sym_path <> sign.sign_path then
      (s.sym_type := mk_Kind; s.sym_rules := [])
  in
  let rec unlink_term t =
    match unfold t with
    | Symb s -> unlink_sym s
    | Prod(a,b)
    | Abst(a,b) -> unlink_term a; unlink_term (snd(unbind b))
    | LLet(a,t,b) -> unlink_term a; unlink_term t; unlink_term (snd(unbind b))
    | Appl(a,b) -> unlink_term a; unlink_term b
    | Meta _ -> assert false
    | Plac _ -> assert false
    | Wild   -> assert false
    | TRef _ -> assert false
    | Bvar _ -> assert false
    | Vari _
    | Patt _
    | Type
    | Kind -> ()
  in
  let unlink_rule r =
    List.iter unlink_term r.lhs;
    unlink_term r.rhs
  in
  let f _ s =
    unlink_term !(s.sym_type);
    Option.iter unlink_term !(s.sym_def);
    List.iter unlink_rule !(s.sym_rules)
  in
  StrMap.iter f !(sign.sign_symbols);
  let f _ {dep_symbols=sm; _} =
    StrMap.iter (fun _ sd -> List.iter unlink_rule sd.rules) sm in
  Path.Map.iter f !(sign.sign_deps);
  StrMap.iter (fun _ s -> unlink_sym s) !(sign.sign_builtins);
  let unlink_ind_data i =
    List.iter unlink_sym i.ind_cons; unlink_sym i.ind_prop in
  let f s i = unlink_sym s; unlink_ind_data i in
  SymMap.iter f !(sign.sign_ind);
  let unlink_cp_pos (_,l,r,_,l_p) =
    unlink_term l; unlink_term r; unlink_term l_p in
  let f s cps = unlink_sym s; List.iter unlink_cp_pos cps in
  SymMap.iter f !(sign.sign_cp_pos)

(** [add_symbol sign expo prop mstrat opaq name pos typ impl notation] adds in
    the signature [sign] a symbol with name [name], exposition [expo],
    property [prop], matching strategy [strat], opacity [opaq], type [typ],
    implicit arguments [impl], no notation, no definition and no rules. [name]
    should not already be used in [sign]. [pos] is the position of the
    declaration (without its definition). The created symbol is returned. *)
let add_symbol : t -> expo -> prop -> match_strat -> bool -> strloc ->
  popt -> term -> bool list -> sym =
  fun sign sym_expo sym_prop sym_mstrat sym_opaq name pos typ impl ->
  let sym =
    create_sym sign.sign_path sym_expo sym_prop sym_mstrat sym_opaq name pos
      (cleanup typ) (minimize_impl impl)
  in
  sign.sign_symbols := StrMap.add name.elt sym !(sign.sign_symbols);
  sym

(** [strip_private sign] removes private symbols from signature [sign]. *)
let strip_private : t -> unit = fun sign ->
  let not_prv sym = not (Term.is_private sym) in
  sign.sign_symbols :=
    StrMap.filter (fun _ s -> not_prv s) !(sign.sign_symbols)

(** [add_rule sign s r] adds the new rule [r] to the symbol [s]. When the rule
    does not correspond to a symbol of signature [sign], it is stored in its
    dependencies. /!\ does not update the decision tree or the critical
    pairs. *)
let add_rule : t -> sym_rule -> unit = fun sign (s,r) ->
  s.sym_rules := !(s.sym_rules) @ [r];
  if s.sym_path <> sign.sign_path then
    let d = try Path.Map.find s.sym_path !(sign.sign_deps)
            with Not_found -> assert false in
    let f = function
      | None -> Some{rules=[r]; nota=None}
      | Some sd -> Some{sd with rules=sd.rules@[r]}
    in
    let sm = StrMap.update s.sym_name f d.dep_symbols in
    let d = {d with dep_symbols=sm} in
    sign.sign_deps := Path.Map.add s.sym_path d !(sign.sign_deps)

(** [add_rules sign s rs] adds the new rules [rs] to the symbol [s]. When the
    rules do not correspond to a symbol of signature [sign], they are stored
    in its dependencies. /!\ does not update the decision tree or the critical
    pairs. *)
let add_rules : t -> sym -> rule list -> unit = fun sign s rs ->
  s.sym_rules := !(s.sym_rules) @ rs;
  if s.sym_path <> sign.sign_path then
    let d = try Path.Map.find s.sym_path !(sign.sign_deps)
            with Not_found -> assert false in
    let f = function
      | None -> Some{rules=rs; nota=None}
      | Some sd -> Some{sd with rules=sd.rules@rs}
    in
    let sm = StrMap.update s.sym_name f d.dep_symbols in
    let d = {d with dep_symbols=sm} in
    sign.sign_deps := Path.Map.add s.sym_path d !(sign.sign_deps)

(** [add_notation sign sym nota] changes the notation of [s] to [n] in
    the signature [sign]. *)
let add_notation : t -> sym -> float notation -> unit = fun sign s n ->
  s.sym_nota := n;
  if s.sym_path <> sign.sign_path then
    let d = try Path.Map.find s.sym_path !(sign.sign_deps)
             with Not_found -> assert false in
    let f = function
      | None -> Some{rules=[]; nota=Some n}
      | Some sd -> Some{sd with nota=Some n}
    in
    let sm = StrMap.update s.sym_name f d.dep_symbols in
    let d = {d with dep_symbols=sm} in
    sign.sign_deps := Path.Map.add s.sym_path d !(sign.sign_deps)

(** [add_builtin sign name sym] binds the builtin [name] to [sym] in the
    signature [sign]. The previous binding, if any, is discarded. *)
let add_builtin : t -> string -> sym -> unit = fun sign name sym ->
  sign.sign_builtins := StrMap.add name sym !(sign.sign_builtins)

(** [add_inductive sign ind_sym ind_cons ind_prop ind_prop_args] add to [sign]
   the inductive type [ind_sym] with constructors [ind_cons], induction
   principle [ind_prop] with [ind_prop_args] arguments. *)
let add_inductive : t -> sym -> sym list -> sym -> int -> int -> unit =
  fun sign ind_sym ind_cons ind_prop ind_nb_params ind_nb_types ->
  let ind_nb_cons = List.length ind_cons in
  let ind = {ind_cons; ind_prop; ind_nb_params; ind_nb_types; ind_nb_cons} in
  sign.sign_ind := SymMap.add ind_sym ind !(sign.sign_ind)

(** [iterate f sign] applies [f] on [sign] and its dependencies
   recursively. *)
let iterate : (t -> unit) -> t -> unit = fun f sign ->
  let visited = Stdlib.ref Path.Set.empty in
  let rec handle sign =
    Stdlib.(visited := Path.Set.add sign.sign_path !visited);
    f sign;
    let dep path _ =
      if not (Path.Set.mem path Stdlib.(!visited)) then
        handle (Path.Map.find path !loaded)
    in
    Path.Map.iter dep !(sign.sign_deps)
  in handle sign

(** [dependencies sign] returns an association list containing (the transitive
    closure of) the dependencies of the signature [sign].  Note that the order
    of the list gives one possible loading order for the signatures. Note also
    that [sign] itself appears at the end of the list. *)
let rec dependencies : t -> (Path.t * t) list = fun sign ->
  (* Recursively compute dependencies for the immediate dependencies. *)
  let f p _ l = dependencies (Path.Map.find p !loaded) :: l in
  let deps = Path.Map.fold f !(sign.sign_deps) [[(sign.sign_path, sign)]] in
  (* Minimize and put everything together. *)
  let rec minimize acc deps =
    let not_here (p,_) =
      let has_p = List.exists (fun (q,_) -> p = q) in
      not (List.exists has_p acc)
    in
    match deps with
    | []      -> List.rev acc
    | d::deps -> minimize ((List.filter not_here d) :: acc) deps
  in
  List.concat (minimize [] deps)
