(*
  - Rajouter le support du multi-objet avec une BitvectorMap.t
  - écrire des tests pour deux objets.
*)
let compose f g x = f (g x)

open Binsec_sse.Types

module ID = struct
  let name = "type_state"
end

module TSLogger = Binsec_sse.Logger.Sub (struct
  let name = "type-state"
end)

let uninitialized_state =
  Binsec_kernel.Bitvector.of_hexstring "0xdeadf00ddeadf00d"

module Automaton = struct
  open Binsec_kernel

  type state_label =
    | Ok of string
    | Error of string
    | Bottom
    | ErrorDefault
    | Impossible

  (** string_of_state_label *)
  let sosl sl =
    match sl with
    | Ok s | Error s -> s
    | Bottom -> "Bottom"
    | ErrorDefault -> "ErrorDefault"
    | Impossible -> "Impossible"

  module Vertex : Graph.Sig.COMPARABLE with type t = state_label = struct
    type t = state_label

    let compare t t' = String.compare (sosl t) (sosl t')
    let hash t = Hashtbl.hash (sosl t)
    let equal t t' = String.equal (sosl t) (sosl t')
  end

  module Edge :
    Graph.Sig.ORDERED_TYPE_DFT with type t = string * Dba.Expr.t * Dba.Expr.t =
  struct
    type t = string * Dba.Expr.t * Dba.Expr.t

    let compare (s, _, _) (s', _, _) = String.compare s s'

    let default =
      let faux = Dba.Expr.constant @@ Bitvector.zero in
      ("", faux, faux)
  end

  module A = struct
    include Graph.Imperative.Digraph.ConcreteLabeled (Vertex) (Edge)

    module Utils = struct
      let pp_vertex ppf vertex = Format.fprintf ppf "%s" @@ sosl vertex

      let pp_edge ppf edge =
        let v, lbl, v' = edge in
        let e_name, expr, expr' = lbl in
        let pp_predicate ppf e =
          if Dba.Expr.is_constant e then Format.fprintf ppf ""
          else Format.fprintf ppf "[%a]" Binsec_sse_stake.pp_dba e
        in
        Format.fprintf ppf "@[<v>(%a) -- %a %s %a --> (%a)@]" pp_vertex v
          pp_predicate expr e_name pp_predicate expr' pp_vertex v'

      let get_edge_name (e : E.t) = match E.label e with n, _, _ -> n

      let find_edges_by_name (n : string) t =
        fold_edges_e
          (fun edge acc ->
            let edge_name, _, _ = E.label edge in
            if String.equal n edge_name then edge :: acc else acc)
          t []

      let is_constructor (e : E.t) =
        let v, _, v' = e in
        let src_ok =
          match v with
          | Bottom -> true
          | Ok _ | Impossible | ErrorDefault | Error _ -> false
        in
        let trgt_ok =
          match v' with
          | ErrorDefault | Error _ | Bottom | Impossible -> false
          | Ok _ -> true
        in
        src_ok && trgt_ok

      let is_destructor (e : E.t) =
        let v, _, v' = e in
        let src_ok =
          match v with
          | Ok _ -> true
          | Bottom | Impossible | ErrorDefault | Error _ -> false
        in
        let trgt_ok =
          match v' with
          | ErrorDefault | Error _ | Ok _ | Impossible -> false
          | Bottom -> true
        in
        src_ok && trgt_ok
    end
  end
end

type sym_kind =
  | Constructor of Automaton.A.E.t
  | Method of Automaton.A.E.t
  | Destructor of Automaton.A.E.t

let map_sym_kind (f : Automaton.A.E.t -> 'b) sym_kind =
  match sym_kind with
  | Constructor l -> f l
  | Method l -> f l
  | Destructor l -> f l

module VertexTbl = struct
  include Hashtbl.Make (struct
    type t = Automaton.A.V.t

    let equal = Automaton.A.V.equal
    let hash = Automaton.A.V.hash
  end)

  let find_match tbl v =
    match find_opt tbl v with
    | Some i -> i
    | None ->
        TSLogger.fatal "The vertex identifier table contains no binding for %a"
          Automaton.A.Utils.pp_vertex v
end

type Binsec_sse.Script.Ast.t += Def_automaton

type ('value, 'model, 'state, 'path, 'a) field_id +=
  | TS_call_stack : ('value, 'model, 'state, 'path, sym_kind list list) field_id
  | TS_call_trace : ('value, 'model, 'state, 'path, string list) field_id
    (*TODO
          'value -> 'value Bitvector.Map.t String.Map.t -> 'value Value.Map.t String.Map.t
        - Le Value.Map.add renvoit l'information sur si il faut forker ou pas et comment.
    *)
  | TS_state : ('value, 'model, 'state, 'path, 'value) field_id

let lb_automaton = Automaton.A.create ()

let make_lb_automaton (arch : Binsec_kernel.Machine.t) : unit =
  let open Binsec_kernel in
  let module MyIsaHelper = (val Isa_helper.get arch) in
  let rax = Dba.LValue.to_expr @@ MyIsaHelper.get_ret () in
  let vrai = Dba.Expr.one in
  let faux = Dba.Expr.zeros (Dba.Expr.size_of rax) in
  (* Vertexes *)
  let nv = Automaton.A.V.create in
  let bottom = nv Bottom in
  let off_ok = nv @@ Ok "off ok" in
  let off_broken = nv @@ Ok "off broken" in
  let on_ok = nv @@ Ok "on ok" in
  let on_broken = nv @@ Ok "on broken" in
  (* Edges *)
  let ne = Automaton.A.E.create in
  let nev e s e' = Automaton.A.E.create e (s, vrai, vrai) e' in
  let buy = nev bottom "buy" off_ok in
  let recycle_ok = nev off_ok "recycle" bottom in
  let recycle_broken = nev off_broken "recycle" bottom in
  let turn_on_ok_ok = nev off_ok "turn_on" on_ok in
  let turn_on_ok_broken = nev off_ok "turn_on" on_broken in
  let turn_off_ok = nev on_ok "turn_off" off_ok in
  let turn_off_broken = nev on_broken "turn_off" off_broken in
  let is_dead_on_ok =
    ne on_ok ("is_dead", vrai, Dba.Expr.equal rax faux) on_ok
  in
  let is_dead_or_broken =
    ne on_broken ("is_dead", vrai, Dba.Expr.diff rax faux) on_broken
  in
  (* automaton *)
  let av = Automaton.A.add_vertex lb_automaton in
  let ae = Automaton.A.add_edge_e lb_automaton in
  List.iter (fun v -> av v) [ bottom; off_ok; off_broken; on_ok; on_broken ];
  List.iter
    (fun e -> ae e)
    [
      buy;
      recycle_ok;
      recycle_broken;
      turn_on_ok_ok;
      turn_on_ok_broken;
      turn_off_ok;
      turn_off_broken;
      is_dead_on_ok;
      is_dead_or_broken;
    ]

module Make (Engine : ENGINE) : EXTENSIONS with type path = Engine.Path.t =
struct
  open Binsec_sse
  open Binsec_kernel
  module Path = Engine.Path

  module ZtMap = Map.Make (struct
    type t = Z.t

    let compare = Z.compare
  end)

  let ts_call_stack_key = Engine.lookup TS_call_stack
  let ts_call_trace_key = Engine.lookup TS_call_trace
  let ts_state_key = Engine.lookup TS_state

  type path = Path.t
  type Ir.builtin += TS_call of string * sym_kind list | TS_return of string
  (* TODO when constructing the automaton, a function cannot be
     a constructor and a normal method at the same time. *)

  let push (path : Path.t) (x : 'a) (key : 'a list Path.key) =
    let curr = Path.get path key in
    Path.set path key (x :: curr)

  let pop (path : Path.t) (key : 'a list Path.key) : 'a option =
    let curr = Path.get path key in
    match curr with
    | t :: q ->
        Path.set path key q;
        Option.some t
    | [] -> None

  let push_call_stack (path : Path.t) (x : sym_kind list) =
    push path x ts_call_stack_key

  let pop_call_stack (path : Path.t) =
    match pop path ts_call_stack_key with
    | Some x -> x
    | None -> TSLogger.fatal "Popped from empty stack"

  let v_id_tbl : int VertexTbl.t = VertexTbl.create 10
  let ts_bitsize : int ref = ref 0

  (** Expects tbl to be empty. *)
  let make_v_id_tbl t (tbl : int VertexTbl.t) : unit =
    TSLogger.debug ~level:4 "State identification:";
    let i = ref 0 in
    Automaton.A.iter_vertex
      (fun v ->
        VertexTbl.add tbl v !i;
        TSLogger.debug ~level:4 "\t* %a identified as %d."
          Automaton.A.Utils.pp_vertex v !i;
        i := !i + 1)
      t

  (* Default error state for the completion *)
  let default_error_state = Automaton.A.(V.create ErrorDefault)

  (* Impossible state for the completion *)
  let impossible_state = Automaton.A.(V.create Impossible)

  (** Ajoute les transitions manquantes dans l'automate. 
      - Les transitions vers l'état ErrorDefault sont ajoutées 
        pour les fonctions manquantes d'un noeud.
      - Les transitions vers l'état Impossible sont ajoutées
        pour les fonctions dont les prédicats ne couvrent pas l'univers.

   *)
  let add_impossible_and_error_states : Automaton.A.t -> Path.t -> unit =
   fun t path ->
    TSLogger.info "completing automaton";
    let open Automaton.A in
    Automaton.A.add_vertex t default_error_state;
    Automaton.A.add_vertex t impossible_state;
    (* Computes l + s keeping uniqueness and ascending order *)
    let rec sorted_list_uniq_insert (l : string list) (s : string) : string list
        =
      match l with
      | [] -> [ s ]
      | t :: q when String.compare t s = 0 -> t :: q
      | t :: q when String.compare t s < 0 -> t :: sorted_list_uniq_insert q s
      | t :: q -> s :: t :: q
    in
    (* computes l - l' keeping ascending order *)
    let rec sorted_list_uniq_diff l l' =
      match l' with
      | [] -> l
      | t' :: q' -> (
          match l with
          | [] -> []
          | t :: q when String.equal t' t -> sorted_list_uniq_diff q q'
          | t :: q when String.compare t' t < 0 ->
              t :: sorted_list_uniq_diff q q'
          | t :: q -> t :: sorted_list_uniq_diff q l')
    in
    (* List of all functions in the automaton *)
    let functions =
      fold_edges_e
        (fun (e : E.t) acc ->
          let name, _, _ = E.label e in
          sorted_list_uniq_insert acc name)
        t []
    in
    let to_iter_v (v : V.t) =
      (* List of edges initially leaving the vertex. *)
      let elist = succ_e t v in
      (* Sorted list of functions leaving the vertex. *)
      let flist =
        elist
        |> List.map (fun e ->
               let n, _, _ = E.label e in
               n)
        |> List.fold_left sorted_list_uniq_insert []
      in
      TSLogger.debug ~level:2 "@[<v>@ [%s]@ Functions present:@ \t* %a@]"
        (Automaton.sosl v)
        (Format.pp_print_list
           ~pp_sep:(fun ppf _ -> Format.fprintf ppf "@ \t* ")
           Format.pp_print_string)
        flist;
      (* Sorted list of missing functions. *)
      let eflist = sorted_list_uniq_diff functions flist in
      TSLogger.debug ~level:2 "@[<v>Missing functions:@ \t* %a@]"
        (Format.pp_print_list
           ~pp_sep:(fun ppf _ -> Format.fprintf ppf "@ \t* ")
           Format.pp_print_string)
        eflist;
      (* Adding missing functions as error transitions. *)
      TSLogger.debug ~level:1 "Completing vertex with:";
      eflist
      |> List.iter (fun name ->
             let vrai = Dba.Expr.constant Bitvector.one in
             let label = (name, vrai, vrai) in
             (* We do not complete the Impossible state *)
             if Automaton.A.V.equal v impossible_state then ()
             else
               let edge = E.create v label default_error_state in
               TSLogger.debug ~level:3 "@[<v>\t@[<v>* %a@]@]" Utils.pp_edge edge;
               add_edge_e t edge);
      (* should be the sequence of edge labels grouped by equal names *)
      let glbl =
        Seq.group (fun (s, _, _) (s', _, _) -> String.equal s s')
        @@ List.to_seq (List.map (fun (_, lbl, _) -> lbl) elist)
      in
      (* list of function_name, predicate_disjonction *)
      let plist =
        Seq.map
          (fun seq ->
            seq
            |> Seq.fold_left
                 (fun (_, pacc) (n, _, p) ->
                   (n, Dba.Expr.binary Dba.Binary_op.Or pacc p))
                 ("", Dba.Expr.zero))
          glbl
      in
      (* Seq of (function, impossible_predicate option) *)
      let impseq =
        Seq.map
          (fun (n, p) ->
            let non_p = Dba.Expr.unary Dba.Unary_op.Not p in
            match Path.check_sat_assuming path non_p with
            | None -> (n, None)
            | Some _ -> (n, Option.some non_p))
          plist
      in
      Seq.iter
        (fun (n, po) ->
          match po with
          | None -> ()
          | Some p ->
              let lbl = (n, Dba.Expr.one, p) in
              let edge = E.create v lbl impossible_state in
              TSLogger.debug ~level:3 "@[<v>\t* %a@]" Utils.pp_edge edge;
              add_edge_e t edge)
        impseq
    in
    (* Iterating on all vertexes *)
    t |> iter_vertex to_iter_v

  let function_intervals = ref Zmap.empty
  let function_addresses : string ZtMap.t ref = ref @@ ZtMap.empty
  let user_errors : Automaton.A.V.t list ref = ref []

  let make_function_intervals
      (symlist : (string * Z.t * Z.t) (* name, addr, size *) list) : unit =
    List.iter
      (fun (s, z, z') ->
        let sgt = Zmap.singleton ~lo:z ~hi:(Z.add z z') s in
        function_intervals := Zmap.union_left !function_intervals sgt)
      symlist

  let make_function_addresses
      (symlist : (string * Z.t * Z.t) (* name, addr, size *) list) : unit =
    List.iter
      (fun (s, z, _) ->
        function_addresses := ZtMap.add z s @@ !function_addresses)
      symlist

  (*
     le call :
       - la liste des transitions a -- l --> a' où l = la fonction.
     Il filtre les transitions en fonction du prédicat d'entrée.
     Il stocke la liste filtrée dans un champ du Path, champ auquel le return se réfère.

     le return :
       - filtre la liste des transitions du path avec le deuxième prédicat et met à jour le state.

     dans le path:
       - Call stack pour stocker les listes de transition.
       - Un champ state : Path.value (Symbolic.Default.Expr.t probablement)
  *)

  let filter_sat path (p : Path.Value.t) : bool =
    match Path.check_sat_assuming_v path p with None -> false | Some _ -> true

  let call (name : string) (quiver : sym_kind list) (path : Path.t) =
    (* Pushing the function called in the call trace *)
    push path name ts_call_trace_key;
    (* Fetching current state *)
    let curr_state = Path.get path ts_state_key in
    (* If the state is uninitialized we push only constructor arrows. *)
    let filtered_quiver =
      if
        (not @@ Path.State.is_symbolic curr_state @@ Path.state path)
        && (Bitvector.equal uninitialized_state @@ Path.eval_v path curr_state)
      then
        List.filter
          (fun es -> match es with Constructor _ -> true | _ -> false)
          quiver
      else
        (* else we filter based on state and call predicate *)
        List.filter
          (fun es ->
            map_sym_kind
              (fun e ->
                let v, lbl, _ = e in
                let _, pred, _ = lbl in
                let state_filter =
                  curr_state
                  |> Path.State.Value.binary Symbolic.State.Eq
                     @@ Path.State.Value.constant
                     @@ Bitvector.of_int ~size:!ts_bitsize
                     @@ VertexTbl.find_match v_id_tbl v
                in
                let predicate_filter = Path.get_value path pred in
                let final_filter =
                  Path.State.Value.binary Symbolic.State.And state_filter
                    predicate_filter
                in
                filter_sat path final_filter)
              es)
          quiver
    in
    push_call_stack path filtered_quiver;
    TSLogger.debug ~level:2 "%s called" name;
    TSLogger.debug ~level:2 "@[<v>Filtered at call:@ %a@]"
      (Format.pp_print_list (fun ppf e ->
           Format.fprintf ppf "%a"
             (fun ppf e -> map_sym_kind (Automaton.A.Utils.pp_edge ppf) e)
             e))
      filtered_quiver;
    Return

  let return (name : string) (path : Path.t) =
    let impossible_state_v =
      Path.State.Value.constant
      @@ Bitvector.of_int ~size:!ts_bitsize
      @@ VertexTbl.find_match v_id_tbl impossible_state
    in
    TSLogger.debug ~level:2 "%s returned" name;
    (* Fetch quiver of available transitions and sort it. *)
    let quiver = pop_call_stack path in
    (* Else we sort transitions in three buckets *)
    let c_list, d_list, m_list =
      let rec partition3 acc l =
        match l with
        | [] -> acc
        | t :: q -> (
            let cl, dl, ml = acc in
            q
            |> partition3
               @@
               match t with
               | Constructor l -> (l :: cl, dl, ml)
               | Destructor l -> (cl, l :: dl, ml)
               | Method l -> (cl, dl, l :: ml))
      in
      partition3 ([], [], []) quiver
    in
    (* One and only one of c_list/d_list/m_list should be non-empty. *)
    (* TODO chech that *)
    let cnt =
      let list_to_int l = if l = [] then 0 else 1 in
      list_to_int c_list + list_to_int d_list + list_to_int m_list
    in
    if cnt <> 1 then
      TSLogger.fatal
        "Automaton allows empty quiver / destructor-constructor-method \
         ambiguity";
    (* List of transition to be taken. *)
    let to_be_taken =
      (* If we are a constructor we construct. *)
      if c_list <> [] then (
        let s =
          Path.State.Value.constant
          @@ Bitvector.of_int ~size:!ts_bitsize
          @@ VertexTbl.find_match v_id_tbl (Automaton.A.V.create Bottom)
        in
        Path.set path ts_state_key s;
        c_list)
      else if m_list <> [] then m_list
      else d_list
    in
    (* filtering based on return predicate *)
    let to_be_taken_filtered =
      List.filter
        (fun e ->
          let _, lbl, _ = e in
          let _, _, pred = lbl in
          let predicate_filter = Path.get_value path pred in
          filter_sat path predicate_filter)
        to_be_taken
    in
    (* Sorting transition that will be taken by first vertex *)
    let sorted_quiver =
      List.to_seq
      @@ List.sort (fun (v, _, _) (v', _, _) -> Automaton.A.V.compare v v')
      @@ to_be_taken_filtered
    in
    (* Grouping transitions by common first vertex *)
    let gquiver =
      Seq.group
        (fun (v, _, _) (v', _, _) -> Automaton.A.V.equal v v')
        sorted_quiver
    in
    (* Making the st variables for each group of vertex. *)
    let st_list =
      List.of_seq
      @@ Seq.map
           (fun (seq : Automaton.A.E.t Seq.t) ->
             match seq () with
             | Seq.Nil -> TSLogger.fatal "Empty sequence in grouped quiver."
             | Seq.Cons (t, _) ->
                 let l = List.of_seq seq in
                 ignore l;
                 if Seq.length seq = 1 then
                   let v, lbl, v' = t in
                   let _, _, p = lbl in
                   let open Path.State.Value in
                   ( v,
                     ite (Path.get_value path p)
                       (constant
                       @@ Bitvector.of_int ~size:!ts_bitsize
                       @@ VertexTbl.find_match v_id_tbl v')
                       (constant
                       @@ Bitvector.of_int ~size:!ts_bitsize
                       @@ VertexTbl.find_match v_id_tbl impossible_state) )
                 else
                   let _, s =
                     let entropy =
                       Path.lookup path
                       (* TODO use minimum size necessary *)
                       @@ Dba.Var.create "entropy" ~bitsize:Size.Bit.bits32
                            ~tag:Dba.Var.Tag.Temp
                     in
                     (ref 0, impossible_state_v)
                     |> List.fold_right (fun (_, (_, _, p), v') (i, acc) ->
                            i := !i + 1;
                            ( i,
                              Path.State.Value.ite
                                (Path.State.Value.binary Symbolic.State.And
                                   (Path.get_value path p)
                                @@ Path.State.Value.binary Symbolic.State.Eq
                                     entropy
                                @@ Path.State.Value.constant
                                @@ Bitvector.of_int ~size:32 !i)
                                (Path.State.Value.constant
                                @@ Bitvector.of_int ~size:!ts_bitsize
                                @@ VertexTbl.find_match v_id_tbl v')
                                acc ))
                        @@ l
                   in
                   let v, _, _ = List.hd l in
                   (v, s))
           gquiver
    in
    (* fetch current state *)
    let current_state = Path.get path ts_state_key in
    (* update state *)
    let rec state_updater (l : (Automaton.A.V.t * Path.Value.t) list) =
      match l with
      | [] -> impossible_state_v
      | (v, p) :: q ->
          let open Path.State.Value in
          ite
            (binary Symbolic.State.Eq current_state
               (constant
               @@ Bitvector.of_int ~size:!ts_bitsize
               @@ VertexTbl.find_match v_id_tbl
               @@ Automaton.A.V.create v))
            p (state_updater q)
    in
    let new_state = state_updater st_list in
    Path.set path ts_state_key new_state;
    (* Assuming we are not on the impossible state *)
    (match
       Path.assume_v path
         (Path.State.Value.binary Symbolic.State.Diff new_state
            impossible_state_v)
     with
    | None -> TSLogger.fatal "Impossible state cannot be avoided."
    | Some _ -> ());
    (* Check if we can be on any error state. *)
    let default_error_state_v =
      Path.State.Value.constant
      @@ Bitvector.of_int ~size:!ts_bitsize
      @@ VertexTbl.find_match v_id_tbl default_error_state
    in
    let predicate =
      List.fold_right
        (fun x acc ->
          Path.State.Value.binary Symbolic.State.Or acc
          @@ Path.State.Value.binary Symbolic.State.Eq new_state
          @@ Path.State.Value.constant
          @@ Bitvector.of_int ~size:!ts_bitsize
          @@ VertexTbl.find_match v_id_tbl x)
        !user_errors
      @@ Path.State.Value.binary Symbolic.State.Eq new_state
           default_error_state_v
    in
    if filter_sat path predicate then (
      let states_bv = Bitvector.Map.keys @@ Path.enumerate_v path new_state in
      TSLogger.debug ~level:4 "Length : %d BV: %a" (List.length states_bv)
        (Format.pp_print_list Bitvector.pp)
        states_bv;
      let states_str =
        VertexTbl.fold
          (fun name id acc ->
            if
              List.exists
                (fun bv ->
                  Bitvector.equal bv @@ Bitvector.of_int ~size:!ts_bitsize id)
                states_bv
            then name :: acc
            else acc)
          v_id_tbl []
      in
      (* TODO Est-ce la bonne manière d'intérompre l'exploration ? *)
      let call_trace : string list =
        let rec popper (_ : unit) =
          match pop path ts_call_trace_key with
          | Some s -> s :: popper ()
          | None -> []
        in
        List.rev @@ popper ()
      in
      TSLogger.fatal
        "@[<v>API misusage.@ The automaton is in the supperposition of \
         states:@ [%a]@ Call trace leading to this state:@ %a@]"
        (Format.pp_print_list
           ~pp_sep:(fun ppf _ -> Format.fprintf ppf " | ")
           Automaton.A.Utils.pp_vertex)
        states_str
        (Format.pp_print_list
           ~pp_sep:(fun ppf _ -> Format.fprintf ppf " -> ")
           Format.pp_print_string)
        call_trace);
    Return

  let initialization_callback (path : Path.t) =
    TSLogger.info "init callback";
    (* Make automaton *)
    make_lb_automaton Engine.isa;
    (* Complete automaton *)
    add_impossible_and_error_states lb_automaton path;
    (* Make state identifiers *)
    make_v_id_tbl lb_automaton v_id_tbl;
    (* Init type state bitsize *)
    ts_bitsize :=
      int_of_float
      @@ (1. +. ((log @@ float_of_int @@ VertexTbl.length v_id_tbl) /. log 2.));
    TSLogger.debug ~level:4 "Type State Bitsize: %d" !ts_bitsize;
    (* Compute list of all error states *)
    user_errors :=
      Automaton.A.fold_vertex
        (fun v acc ->
          match v with Error _ | Automaton.ErrorDefault -> v :: acc | _ -> acc)
        lb_automaton []

  (* regarder dans exec.ml ou script.ml comment c'est fait *)
  let grammar_extension =
    [
      Dyp.Add_rules
        [
          ( ( "decl",
              [
                Dyp.Regexp (RE_String "def"); Dyp.Regexp (RE_String "automaton");
              ],
              "default_priority",
              [] ),
            fun _ -> function
              | [ _; _ ] -> (Binsec_script.Syntax.Decl Def_automaton, [])
              | _ -> assert false );
        ];
    ]

  let list =
    [
      Initialization_callback initialization_callback;
      Grammar_extension grammar_extension;
      Command_handler
        (fun _ (env : Script.env) path : bool ->
          let symbol_assoc_list =
            Automaton.A.fold_edges_e
              (fun e l ->
                let e_name = Automaton.A.Utils.get_edge_name e in
                let addr =
                  try
                    Bitvector.value_of
                    @@ Path.eval path
                         (env.lookup_symbol e_name Dba.Var.Tag.Value)
                  with _ ->
                    TSLogger.warning "Le symbole n'existe pas : %s" e_name;
                    Bitvector.value_of @@ Bitvector.zero
                in
                let size =
                  try
                    Bitvector.value_of
                    @@ Path.eval path
                         (env.lookup_symbol e_name Dba.Var.Tag.Size)
                  with _ ->
                    TSLogger.warning "Le symbole %s n'a pas de taille" e_name;
                    Bitvector.value_of @@ Bitvector.zero
                in
                (e_name, addr, size) :: l)
              lb_automaton []
          in
          make_function_intervals symbol_assoc_list;
          make_function_addresses symbol_assoc_list;
          true);
      Fetch_hook
        {
          scope = None;
          stage = Early;
          callback =
            (fun va ->
              match
                ZtMap.find_opt (Virtual_address.to_bigint va)
                @@ !function_addresses
              with
              | Some elt ->
                  let quiver =
                    Automaton.A.fold_edges_e
                      (fun e acc ->
                        let _, lbl, _ = e in
                        let n, _, _ = lbl in
                        if String.equal n elt then
                          if Automaton.A.Utils.is_constructor e then
                            Constructor e :: acc
                          else if Automaton.A.Utils.is_destructor e then
                            Destructor e :: acc
                          else Method e :: acc
                        else acc)
                      lb_automaton []
                    |> List.sort (fun e e' ->
                           match (e, e') with
                           | Constructor _, Constructor _ -> 0
                           | Destructor _, Destructor _ -> 0
                           | Method _, Method _ -> 0
                           | Constructor _, Destructor _ -> -1
                           | Destructor _, Constructor _ -> 1
                           | Constructor _, Method _ -> -2
                           | Method _, Constructor _ -> 2
                           | Destructor _, Method _ -> -1
                           | Method _, Destructor _ -> 1)
                  in
                  TSLogger.debug ~level:1 "Inserting call hook for %s" elt;
                  Option.some
                  @@ Ir.Graph.of_script va
                       (String.cat "Hook_call_" elt)
                       [ Opcode (Builtin (TS_call (elt, quiver))) ]
              | None -> None);
        };
      Instrumentation_routine
        (fun graph ->
          Revision.iter_new_vertex
            (fun vertex ->
              let node = Revision.node graph vertex in
              match node with
              (* Insert TS_return builtin *)
              | Terminator { kind = Goto { target = _; tag = Return; _ }; _ }
              | Terminator { kind = Jump { target = _; tag = Return; _ }; _ }
                -> (
                  let label = Ir.label_of node in
                  let addr =
                    match label with
                    | Instruction i -> Instruction.address i
                    | Hook { addr; _ } -> addr
                  in
                  match
                    Zmap.find_opt (Virtual_address.to_bigint addr)
                    @@ !function_intervals
                  with
                  | Item { elt; _ } ->
                      TSLogger.debug ~level:1 "Inserting return hook for %s" elt;
                      Revision.insert_before graph vertex
                        (Builtin (TS_return elt))
                  | Empty -> ())
              | _ -> ())
            graph);
      Builtin_printer
        (fun ppf -> function
          | TS_call (target, _) ->
              Format.fprintf ppf "typestate call - %s" target;
              true
          | TS_return target ->
              Format.fprintf ppf "typestate return - %s" target;
              true
          | _ -> false);
      Builtin_resolver
        (function
        | TS_call (target, quiver) -> Call (call target quiver)
        | TS_return target -> Call (return target)
        | _ -> Unknown);
    ]
end

module Plugin : PLUGIN = struct
  include ID

  let fields : (module PATH) -> field list =
   fun path ->
    let module Path = (val path) in
    [
      Field
        {
          id = TS_state;
          default = Path.Value.constant @@ uninitialized_state;
          copy = None;
          merge = None;
        };
      Field { id = TS_call_stack; default = []; copy = None; merge = None };
      Field { id = TS_call_trace; default = []; copy = None; merge = None };
    ]

  let extensions :
      type a. (module ENGINE with type Path.t = a) -> a extension list =
   fun engine ->
    let module Extensions = Make ((val engine)) in
    TSLogger.info "Type state activated.";
    Extensions.list
end
