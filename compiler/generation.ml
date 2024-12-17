open Extracted.Imp
open Format

let pretty_printer m = printf "Ok: %s\n" (m_name m)
let pp_ident fmt ident = fprintf fmt "var_%i" ident
let pp_fun_name fmt ident = fprintf fmt "fun_%s" ident
let todo fmt = fprintf fmt "not yet implemented"

let pp_const fmt c =
  match c with
  | CBool c -> fprintf fmt "%s" (if c then "1 /* true */" else "0 /* false */")
  | _ -> fprintf fmt "not yet implemented"

let pp_var fmt v = fprintf fmt "%a" pp_ident (fst v)

let pp_op fmt op =
  match op with
  | Bop_and -> fprintf fmt "&&"
  | Bop_or -> fprintf fmt "||"
  | Bop_xor -> fprintf fmt "^"
  | _ -> todo fmt

let rec pp_expr fmt exp =
  match exp with
  | EConst c -> fprintf fmt "%a" pp_const c
  | EInput _ -> fprintf fmt ""
  | EVar v -> fprintf fmt "%a" pp_var v
  | EBinop (op, e1, e2) ->
      fprintf fmt "(%a %a@ %a)" pp_expr e1 pp_op op pp_expr e2
  | _ -> todo fmt

let rec pp_stmt fmt stmt =
  match stmt with
  | SAssign (x, e) -> fprintf fmt "%s %a =@ %a;" "char" pp_ident x pp_expr e
  | SSeq (s1, s2) -> fprintf fmt "%a \n %a" pp_stmt s1 pp_stmt s2
  | SNop -> fprintf fmt ""

let pp_coq_method cm =
  printf "char %a() {@[<h4>%a\n return %a;\n@]}" pp_fun_name (m_name cm) pp_stmt
    (m_body cm) pp_var (m_out cm)
