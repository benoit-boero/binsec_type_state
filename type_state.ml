module ID = struct
  let name="type_state"
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
  module Edge : Graph.Sig.ORDERED_TYPE_DFT = struct
    type t = string * Dba.Expr.t * Dba.Expr.t
    let compare = fun (s,_,_) (s',_,_) -> String.compare s s'
    let default = let faux = Dba.Expr.constant @@ Bitvector.zero in
      ("", faux, faux)
  end
  module A = Graph.Imperative.Digraph.ConcreteLabeled(Vertex)(Edge)
end

module Make (Engine : ENGINE) : EXTENSIONS with type path = Engine.Path.t =
struct

  module Path = Engine.Path

  type path = Path.t

  let list = []
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
