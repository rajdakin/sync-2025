let generate_rules base =
  Printf.printf

{|(rule
  (deps main.exe (source_tree examples/%s.mls))
  (action
    (with-accepted-exit-codes
      (or 0 1)
      (with-outputs-to %s.output (run ./main.exe examples/%s.mls))
    )
  )
)

(rule
  (alias runtest)
  (deps (source_tree examples/%s.expected) %s.output)
  (action (diff examples/%s.expected %s.output))
)
|}
    base base base base base base base

let () =
  Sys.readdir "examples"
  |> Array.to_list
  |> List.sort String.compare
  |> List.filter_map (Filename.chop_suffix_opt ~suffix:".mls")
  |> List.iter generate_rules
