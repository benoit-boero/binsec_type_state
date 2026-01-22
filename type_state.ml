module ID = struct
  let name = "type_state"
end

open Binsec_sse.Types

module Automaton = struct
  open Binsec_kernel

  module Vertex : Graph.Sig.COMPARABLE = struct
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

let lb_automaton = ref @@ Automaton.A.create ()
let make_lb_automaton (_ : unit) = ()

module Make (Engine : ENGINE) : EXTENSIONS with type path = Engine.Path.t =
struct
  open Binsec_sse
  open Binsec_kernel
  module Path = Engine.Path

  type path = Path.t
  type Ir.builtin += TS_call of Virtual_address.t | TS_return

  (*
  Utiliser -> Binsec_base.Zmap !!
  
  module Zmap = Map.Make
    (struct
      type t = string
      let compare = String.compare
    end)
*)

  let zmap : Z.t Interval.t Zmap.t ref = ref Zmap.empty
  let make_zmap (_ : (string * Z.t) list) : unit = ()

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

  let list =
    [
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
                  with _ -> Bitvector.value_of @@ Bitvector.zero
                in
                (e_name, addr) :: l)
              !lb_automaton []
          in
          make_zmap symbol_assoc_list;
          true);
      (* Utiliser fetch hook pour pouvoir directement instrumenter l'adresse
             sse/loader/ir.mli:132
             stmt list : [Opcode (Builtin TS_call)]

         garder le instrumentation routine pour les return.
         l'adresse à laquelle on est est dans label : Ir.label
           (soit une instruction assembleur -> Instruction.address
            soit un hook (qui contient l'adresse))
      *)
      Instrumentation_routine
        (fun graph ->
          Revision.iter_new_vertex
            (fun vertex ->
              match Revision.node graph vertex with
              (* Insert TS_call builtin *)
              (* On veut instrumenter l'adresse de la fonction pas l'adresse du call *)
              | Fallthrough { kind = Goto { tag = Call { base; _ }; _ }; _ }
              | Terminator { kind = Goto { tag = Call { base; _ }; _ }; _ }
              | Terminator { kind = Jump { tag = Call { base; _ }; _ }; _ } ->
                  Revision.insert_before graph vertex (Builtin (TS_call base))
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

  (* TODO mettre dans initial callback *)
  let _ = make_lb_automaton ()

  let extensions :
      type a. (module ENGINE with type Path.t = a) -> a extension list =
   fun engine ->
    let module Extensions = Make ((val engine)) in
    Extensions.list
end
