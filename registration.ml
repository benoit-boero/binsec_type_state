module Namespace =
  Binsec_cli.Cli.Make_from_logger
    (Type_state.TSLogger)
    (struct
      let name = "Type State"
      let shortname = "type-state"
    end)

let () =
  Binsec_cli_sse.Plugins.register ~is_enabled:Namespace.is_enabled (fun () ->
      (module Type_state.Plugin))
