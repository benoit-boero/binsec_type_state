module ID = struct
  let name = "type_state"
end

module TSLogger = Binsec_sse.Logger.Sub (struct
  let name = "type_state"
end)

type Binsec_sse.Script.Ast.t += Def_automaton

open Binsec_sse.Types

module Automaton = struct
  open Binsec_kernel

  module Vertex : Graph.Sig.COMPARABLE with type t = string = struct
    type t = string

    let compare = String.compare
    let hash = Hashtbl.hash
    let equal = String.equal
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
      let get_edge_name (e : E.t) = match E.label e with n, _, _ -> n
    end
  end
end

let lb_automaton = Automaton.A.create ()

let make_lb_automaton (arch : Binsec_kernel.Machine.t) : unit =
  let open Binsec_kernel in
  let module MyIsaHelper = (val Isa_helper.get arch) in
  let vrai = Dba.Expr.constant @@ Bitvector.one in
  let faux = Dba.Expr.constant @@ Bitvector.zero in
  let rax = MyIsaHelper.get_return_address () in
  (* Vertexes *)
  let nv = Automaton.A.V.create in
  let bottom = nv "bottom" in
  let off_ok = nv "off ok" in
  let off_broken = nv "off broken" in
  let on_ok = nv "on ok" in
  let on_broken = nv "on broken" in
  let impossible_state = nv "Impossible state" in
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
  let is_broken_on_ok =
    ne on_ok ("is_broken", vrai, Dba.Expr.equal rax faux) on_ok
  in
  (* TODO impossible transitions *)
  let is_broken_on_broken =
    ne on_broken ("is_broken", vrai, Dba.Expr.equal rax vrai) on_broken
  in
  (* automaton *)
  let av = Automaton.A.add_vertex lb_automaton in
  let ae = Automaton.A.add_edge_e lb_automaton in
  List.iter
    (fun v -> av v)
    [ bottom; off_ok; off_broken; on_ok; on_broken; impossible_state ];
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
      is_broken_on_ok;
      is_broken_on_broken;
    ]

module Make (Engine : ENGINE) : EXTENSIONS with type path = Engine.Path.t =
struct
  open Binsec_sse
  open Binsec_kernel
  module Path = Engine.Path

  type path = Path.t
  type Ir.builtin += TS_call of Virtual_address.t | TS_return

  let function_intervals = ref Zmap.empty

  let make_function_intervals
      (symlist : (string * Z.t * Z.t) (* name, addr, size *) list) : unit =
    List.iter
      (fun (s, z, z') ->
        let sgt = Zmap.singleton ~lo:z ~hi:(Z.add z z') s in
        function_intervals := Zmap.union_left !function_intervals sgt)
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
  let call _ (_ : Path.t) = Return
  let return (_ : Path.t) = Return

  let initialization_callback (_ : Path.t) =
    TSLogger.debug ~level:1 "Initialization_callback";
    make_lb_automaton Engine.isa

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
          TSLogger.debug ~level:1 "Command_handler";
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
                    TSLogger.debug ~level:1
                      "Warning : Le symbole n'existe pas : %s" e_name;
                    (*TODO warning quand le symbole n'existe pas ?*)
                    Bitvector.value_of @@ Bitvector.zero
                in
                let size =
                  try
                    Bitvector.value_of
                    @@ Path.eval path
                         (env.lookup_symbol e_name Dba.Var.Tag.Size)
                  with _ ->
                    (*TODO warning quand le symbole n'a pas de taille ?*)
                    TSLogger.debug ~level:1
                      "Warning : Le symbole %s n'a pas de taille" e_name;
                    Bitvector.value_of @@ Bitvector.zero
                in
                (e_name, addr, size) :: l)
              lb_automaton []
          in
          make_function_intervals symbol_assoc_list;
          true);
      (* Utiliser fetch hook pour pouvoir directement instrumenter l'adresse
             sse/loader/ir.mli:132
             stmt list : [Opcode (Builtin TS_call)]

         garder le instrumentation routine pour les return.
         l'adresse à laquelle on est est dans label : Ir.label
           (soit une instruction assembleur -> Instruction.address
            soit un hook (qui contient l'adresse))
      *)
      Fetch_hook
        {
          scope = None;
          stage = Early;
          callback =
            (fun va ->
              match
                Zmap.find_opt (Virtual_address.to_bigint va)
                @@ !function_intervals
              with
              | Item { elt; _ } ->
                  Format.fprintf Format.std_formatter
                    "Inserting call hook for %s" elt;
                  Option.some
                  @@ Ir.Graph.of_script va
                       (String.cat "Hook_call_" elt)
                       [ Opcode (Builtin (TS_call va)) ]
              | Empty -> None);
        };
      Instrumentation_routine
        (fun graph ->
          Revision.iter_new_vertex
            (fun vertex ->
              let node = Revision.node graph vertex in
              let _ = Ir.label_of node in
              match node with
              (* Insert TS_return builtin *)
              | Terminator { kind = Goto { target = _; tag = Return; _ }; _ } ->
                  Revision.insert_before graph vertex (Builtin TS_return)
              | Terminator { kind = Jump { target = _; tag = Return; _ }; _ } ->
                  Revision.insert_before graph vertex (Builtin TS_return)
              | _ -> ())
            graph);
      Builtin_printer
        (fun ppf -> function
          | TS_call target ->
              Format.fprintf ppf "typestate call %a" Virtual_address.pp target;
              true
          | TS_return ->
              Format.fprintf ppf "typestate return";
              true
          | _ -> false);
      Builtin_resolver
        (function
        | TS_call target -> Call (call target)
        | TS_return -> Call return
        | _ -> Unknown);
    ]
end

module Plugin : PLUGIN = struct
  include ID

  let fields : (module PATH) -> field list = fun _ -> []

  let extensions :
      type a. (module ENGINE with type Path.t = a) -> a extension list =
   fun engine ->
    let module Extensions = Make ((val engine)) in
    Extensions.list
end
