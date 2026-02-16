(*
  - Rajouter le support du multi-objet avec une BitvectorMap.t
  - écrire des tests pour deux objets.
*)

open Binsec_sse.Types

module ID = struct
  let name = "type_state"
end

module TSLogger = Binsec_sse.Logger.Sub (struct
  let name = "type-state"
end)

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

      let is_constructor (s : string) (t : t) =
        false
        |> fold_edges_e
             (fun edge acc ->
               let v, e, v' = edge in
               if acc then acc
               else
                 let target_ok =
                   match v' with
                   | ErrorDefault | Error _ | Bottom | Impossible -> false
                   | Ok _ -> true
                 in
                 let n, _, _ = e in
                 if String.equal n s && v = Bottom && target_ok then (
                   TSLogger.debug ~level:1 "found constructor: %a" pp_edge edge;
                   true)
                 else false)
             t
    end
  end
end

type Binsec_sse.Script.Ast.t += Def_automaton

type ('value, 'model, 'state, 'path, 'a) field_id +=
  | TS_call_stack :
      ('value, 'model, 'state, 'path, Automaton.A.E.t list list) field_id
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
  let ts_state_key = Engine.lookup TS_state

  let push (path : Path.t) (x : Automaton.A.E.t list) =
    let curr = Path.get path ts_call_stack_key in
    Path.set path ts_call_stack_key (x :: curr)

  let pop (path : Path.t) =
    let curr = Path.get path ts_call_stack_key in
    match curr with
    | t :: q ->
        Path.set path ts_call_stack_key q;
        t
    | [] -> TSLogger.fatal "Popped from empty stack."

  type path = Path.t

  (* TODO rajouter les destructeurs *)
  type is_constructor = bool
  type Ir.builtin += TS_call of string * is_constructor | TS_return of string
  (* TODO when constructing the automaton, a function cannot be
     a constructor and a normal method at the same time. *)

  (** Ajoute les transitions manquantes dans l'automate. 
      - Les transitions vers l'état ErrorDefault sont ajoutées 
        pour les fonctions manquantes d'un noeud.
      - Les transitions vers l'état Impossible sont ajoutées
        pour les fonctions dont les prédicats ne couvrent pas l'univers.

        TODO ajouter la même chose pour le prédicat de call.
   *)
  let add_impossible_and_error_states : Automaton.A.t -> Path.t -> unit =
   fun t path ->
    let open Automaton.A in
    (* Default error state for the completion *)
    let default_error_state = V.create ErrorDefault in
    (* Impossible state for the completion *)
    let impossible_state = V.create Impossible in
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

  (*
TODO
  Il vaut mieux flagger les edge comme "constructeur" plutôt que le builtin.
  
  *)

  let call (name : string) (is_constructor : bool) (path : Path.t) =
    let unfiltered_edge_list =
      (* TODO filtrer d'abbord en fonction de l'état puis en fonction des prédicats.
              faire qu'une requête au solveur en vérifiant les deux en mm temps avec un ET *)
      (* TODO déplacer ça au moment de l'instrumentation *)
      Automaton.A.Utils.find_edges_by_name name lb_automaton
    in
    (*TODO update constructor behaviour one day *)
    let state =
      if is_constructor then
        Path.set path ts_state_key @@ Path.State.Value.constant
        (* TODO utiliser des identifiants uniques *)
        @@ Bitvector.of_int ~size:63 (Automaton.A.V.hash Bottom)
      else ();
      Path.get path ts_state_key
    in
    let edge_list =
      List.filter
        (fun e ->
          let v, lbl, _ = e in
          let _, pred, _ = lbl in
          (* TODO est-ce que is_zero = Unknown => un possible ? *)
          let predicate_filter =
            (* TODO remplacer is_zero par check_sat_assume *)
            match Path.is_zero path pred with
            | Unknown ->
                TSLogger.warning
                  "Solver returned unknown while filtering edge at call site.";
                true
            | True -> false
            | False -> true
          in
          let v_value =
            Path.State.Value.constant
            @@ Bitvector.of_int ~size:63 (Automaton.A.V.hash v)
          in
          let state_filter =
            match
              Path.State.Value.binary Symbolic.State.Eq v_value state
              (* TODO replace is_zero *)
              |> Path.is_zero_v path
            with
            | Unknown ->
                TSLogger.warning
                  "Solver returned unknown while filtering edge at call site.";
                true
            | True -> false
            | False -> true
          in
          state_filter && predicate_filter)
        unfiltered_edge_list
    in
    TSLogger.debug ~level:2 "%s called" name;
    TSLogger.debug ~level:2 "@[<v>Filtered at call:@ %a@]"
      (Format.pp_print_list Automaton.A.Utils.pp_edge)
      edge_list;
    push path edge_list;
    Return

  let return (name : string) (path : Path.t) =
    TSLogger.debug ~level:2 "%s returned" name;
    (* Fetch quiver of available transitions and sort it. *)
    let quiver =
      List.to_seq
      @@ List.sort (fun (v, _, _) (v', _, _) -> Automaton.A.V.compare v v')
      @@ pop path
    in
    (* Grouping transitions by common first vertex *)
    let gquiver =
      Seq.group (fun (v, _, _) (v', _, _) -> Automaton.A.V.equal v v') quiver
    in
    (* Making the st variables for each group of vertex. *)
    let st_list =
      List.of_seq
      @@ Seq.map
           (fun (seq : Automaton.A.E.t Seq.t) ->
             match seq () with
             | Seq.Nil -> TSLogger.fatal "Empty sequence in grouped quiver."
             | Seq.Cons (t, _) ->
                 if Seq.length seq = 1 then
                   let v, lbl, v' = t in
                   let _, _, p = lbl in
                   let open Path.State.Value in
                   ( v,
                     ite (Path.get_value path p)
                       (constant @@ Bitvector.of_int ~size:63
                      @@ Automaton.A.V.hash v')
                       (constant @@ Bitvector.of_int ~size:63
                       @@ Automaton.A.V.hash Impossible) )
                 else
                   (*
                   let entropy =
                     Dba.Var.create "entropy" ~bitsize:Size.Bit.bits32
                       ~tag:Dba.Var.Tag.Temp
                   in
                   let sentropy = Path.symbolize path entropy in
                   Seq.fold_left
                   (fun acc (_,(_,_,p),v') -> )
                   None
                   seq
                    in
                    *)
                   TSLogger.fatal "TODO" (*TODO*))
           gquiver
    in
    (* fetch current state *)
    let current_state = Path.get path ts_state_key in
    (* update state *)
    let rec state_updater (l : (Automaton.A.V.t * Path.Value.t) list) =
      match l with
      | [] ->
          (* TODO quand le hash sera remplacé par un identifiant unique,
             remplacer 63 par la taille minimale nécessaire. *)
          Path.State.Value.constant @@ Bitvector.of_int ~size:63
          @@ Automaton.A.V.hash Impossible
      | (v, p) :: q ->
          let open Path.State.Value in
          ite
            (binary Symbolic.State.Eq current_state
               (constant @@ Bitvector.of_int ~size:63 @@ Automaton.A.V.hash v))
            p (state_updater q)
    in
    Path.set path ts_state_key @@ state_updater st_list;
    (*
    TODO
      - Assume not impossible Path.State.assume
      - Check if error state
    *)
    Return

  let initialization_callback (path : Path.t) =
    make_lb_automaton Engine.isa;
    add_impossible_and_error_states lb_automaton path

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
                  if Automaton.A.Utils.is_constructor elt lb_automaton then (
                    TSLogger.debug ~level:1 "Inserting constructor hook for %s"
                      elt;
                    Option.some
                    @@ Ir.Graph.of_script va
                         (String.cat "Hook_constructor_" elt)
                         [ Opcode (Builtin (TS_call (elt, true))) ])
                  else (
                    TSLogger.debug ~level:1 "Inserting call hook for %s" elt;
                    Option.some
                    @@ Ir.Graph.of_script va
                         (String.cat "Hook_call_" elt)
                         [ Opcode (Builtin (TS_call (elt, false))) ])
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
          | TS_call (target, isc) ->
              Format.fprintf ppf "typestate call - %s (%s)" target
              @@ if isc then "constructor" else "method";
              true
          | TS_return target ->
              Format.fprintf ppf "typestate return - %s" target;
              true
          | _ -> false);
      Builtin_resolver
        (function
        | TS_call (target, isc) -> Call (call target isc)
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
          default =
            Path.State.Value.constant @@ Binsec_kernel.Bitvector.zeros 63;
          copy = None;
          merge = None;
        };
      Field { id = TS_call_stack; default = []; copy = None; merge = None };
    ]

  let extensions :
      type a. (module ENGINE with type Path.t = a) -> a extension list =
   fun engine ->
    let module Extensions = Make ((val engine)) in
    TSLogger.info "Type state activated.";
    Extensions.list
end
