module ID = struct
  let name="type_state"
end

open Binsec_sse.Types
open Binsec_kernel

(** Custom finite state automaton module used in this plugin. *)
module AutomatonMaker = struct
  module type AUTOMATON_SPEC = sig
    type name
    type key

    val pp_name : Format.formatter -> name -> unit
    val pp_key : Format.formatter -> key -> unit
    val compare : key -> key -> int
  end

  (* Utiliser ocamlgraph ? *)
  (* Pas grave de faire un lookup à chaque lien Dba -> state *)
  module Make (Spec : AUTOMATON_SPEC) = struct
    type name = Spec.name
    type key = Spec.key
    type state_kind = BOTTOM | NORMAL | ERROR | IMPOSSIBLE

    (* pas besoin de ref ici. *)
    type transition = { symbol : key; destination : typestate ref }

    and typestate = {
      name : name option;
      kind : state_kind;
      quiver : transition Queue.t;
    }

    type t = {
      name : name;
      state_list : typestate list;
      initial_state : typestate;
      default_error : typestate;
      (* Le current_state sera plutôt une variable dba. *)
      current_state : typestate Seq.t ref;
    }

    let create_transition (symbol : key) (dest : typestate) : transition =
      { symbol; destination = ref dest }

    let create_typestate (name : name option) (kind : state_kind) =
      { name; kind; quiver = Queue.create () }

    let push_transition (t : transition) typestate : unit =
      match typestate with { quiver; _ } -> Queue.push t quiver

    let rec push_transitions (transition_list : transition list) typestate :
        unit =
      match transition_list with
      | t :: q ->
          push_transition t typestate;
          push_transitions q typestate
      | [] -> ()

    let create (name : name) initial_state default_error
        (state_list : typestate list) : t =
      {
        name;
        state_list;
        initial_state;
        default_error;
        current_state = List.to_seq [ initial_state ] |> ref;
      }

    (** Given an input automaton and a symbol, computes the evolution 
        of the current state based on the reading of that symbol.*)
    let update_state t (key : key) =
      let compute_transition transition =
        if transition.symbol = key then !(transition.destination)
        else t.default_error
      in
      let compute_typestate typestate =
        let seq = Queue.to_seq typestate.quiver in
        Seq.map (fun t -> compute_transition t) seq
      in
      let new_state =
        Seq.concat
        @@ Seq.map (fun ts -> compute_typestate ts) !(t.current_state)
      in
      t.current_state = ref new_state

    let pp_typestate_name (ppf : Format.formatter) (ts : typestate) =
      match ts.name with
      | None -> Format.fprintf ppf ""
      | Some value -> Format.fprintf ppf "%a" Spec.pp_name value

    let pp_transition (ppf : Format.formatter) transition : unit =
      Format.fprintf ppf "--- %a ---> %a" Spec.pp_key transition.symbol
        pp_typestate_name !(transition.destination)

    let pp_typestate (ppf : Format.formatter) typestate : unit =
      Format.fprintf ppf "@[<v>{%a}:@;@[<v>%a@]@]" pp_typestate_name typestate
        (Format.pp_print_seq ~pp_sep:Format.pp_print_space pp_transition)
        (Queue.to_seq typestate.quiver)

    let pp (ppf : Format.formatter) automaton : unit =
      Format.fprintf ppf "@[<v><%a>:@;%a@]" Spec.pp_name automaton.name
        (Format.pp_print_list
           ~pp_sep:(fun ppf (_ : unit) -> Format.pp_print_break ppf 0 1)
           pp_typestate)
        automaton.state_list
  end
end

module AutomatonSpec : AutomatonMaker.AUTOMATON_SPEC with type name = string =
struct
  type name = string
  type key = string * Dba.Expr.t * Dba.Expr.t

  let pp_name (ppf : Format.formatter) name = Format.fprintf ppf "%s" name

  let pp_key (ppf : Format.formatter) key =
    match key with str, _, _ -> Format.fprintf ppf "%s" str

  let compare (k : key) (k' : key) : int =
    match (k, k') with (str, _, _), (str', _, _) -> String.compare str str'
end

module Automaton = AutomatonMaker.Make (AutomatonSpec)

let test () : unit =
  let _ = Automaton.create_typestate (Some "a") Automaton.NORMAL in
  ()

(*
let make_lb_automaton =
  let initial_state =
    Automaton.create_typestate (Some "Bottom") Automaton.BOTTOM
  in
  let default_error =
    Automaton.create_typestate (Some "Error") Automaton.ERROR
  in
  let off_ok = Automaton.create_typestate (Some "Off Ok") Automaton.NORMAL in
  let on_ok = Automaton.create_typestate (Some "On Ok") Automaton.NORMAL in
  let on_broken =
    Automaton.create_typestate (Some "On Broken") Automaton.NORMAL
  in
  let off_broken =
    Automaton.create_typestate (Some "Off Broken") Automaton.NORMAL
  in
  ()
*)

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
