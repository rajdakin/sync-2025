let generate_rules i base =
  Printf.printf
{|%s(rule
  (deps (source_tree %s.mls))
  (target %s.output)
  (action
    (run ../main.exe -test-mode %s.mls)
  )
)
(rule
  (alias runtest)
  (deps (source_tree %s.expected) %s.output)
  (action (diff %s.expected %s.output))
)
|}
    (if i = 0 then "" else "\n") base base base base base base base

let () =
  Sys.readdir "examples"
  |> Array.to_list
  |> List.sort String.compare
  |> List.filter_map (Filename.chop_suffix_opt ~suffix:".mls")
  |> List.iteri generate_rules
