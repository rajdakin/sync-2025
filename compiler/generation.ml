open Extracted.Imp
open Format

let pretty_printer m = printf "Ok: %s\n" (m_name m)
let pp_ident fmt ident = fprintf fmt "var_%i" ident
let pp_fun_name fmt ident = fprintf fmt "fun_%s" ident

let pp_const fmt c =
  match c with
  | CBool c -> fprintf fmt "%s" (if c then "1 /* true */" else "0 /* false */")
  | CInt i -> fprintf fmt "%i" i
  | CVoid -> fprintf fmt "void"

let pp_typ fmt typ =
  match typ with
  | TVoid -> fprintf fmt "void"
  | TBool -> fprintf fmt "char"
  | TInt -> fprintf fmt "int"

let pp_var fmt v = fprintf fmt "%a" pp_ident (fst v)

let pp_unop fmt op =
  match op with Uop_not -> fprintf fmt "~" | Uop_neg -> fprintf fmt "-"

let pp_binop fmt op =
  match op with
  | Bop_and -> fprintf fmt "&&"
  | Bop_or -> fprintf fmt "||"
  | Bop_xor -> fprintf fmt "^"
  | Bop_plus -> fprintf fmt "+"
  | Bop_minus -> fprintf fmt "-"
  | Bop_mult -> fprintf fmt "*"
  | Bop_div -> fprintf fmt "/"
  | Bop_eq -> fprintf fmt "="
  | Bop_le -> fprintf fmt "<="
  | Bop_lt -> fprintf fmt "<"
  | Bop_ge -> fprintf fmt ">="
  | Bop_gt -> fprintf fmt ">"

let rec pp_expr fmt exp =
  match exp with
  | EConst c -> fprintf fmt "%a" pp_const c
  | EInput _ -> ()
  | EVar v -> fprintf fmt "%a" pp_var v
  | EUnop (op, e) -> fprintf fmt "(%a %a)" pp_unop op pp_expr e
  | EBinop (op, e1, e2) ->
      fprintf fmt "(%a %a@ %a)" pp_expr e1 pp_binop op pp_expr e2
  | EIfte (cond, e1, e2) ->
      fprintf fmt "(%a) ? (%a) : (%a)" pp_expr cond pp_expr e1 pp_expr e2

let is_empty_sassign stmt =
  match stmt with SAssign (_, EInput _) -> true | _ -> false

let get_var_typ var env =
  snd (List.find (fun (name, _) -> name = var) (m_vars env))

let rec pp_stmt env fmt stmt =
  match stmt with
  | SAssign (_, EInput _) -> ()
  | SSeq (s1, s2) when is_empty_sassign s1 -> pp_stmt env fmt s2
  | SSeq (s1, s2) when is_empty_sassign s2 -> pp_stmt env fmt s1
  | SAssign (x, e) ->
      fprintf fmt "%a %a =@ %a;" pp_typ (get_var_typ x env) pp_ident x pp_expr e
  | SSeq (s1, s2) -> fprintf fmt "%a \n %a" (pp_stmt env) s1 (pp_stmt env) s2
  | SNop -> fprintf fmt ""

let pp_binder fmt binder = fprintf fmt "%a" pp_ident (fst binder)
let pp_arg fmt arg = fprintf fmt "%a %a" pp_typ (snd arg) pp_binder arg

let pp_args fmt (args : binder list) =
  Format.pp_print_list
    ~pp_sep:(fun fmt () -> fprintf fmt ",")
    (fun fmt arg -> fprintf fmt "%a" pp_arg arg)
    fmt args

let pp_coq_method cm =
  printf "%a %a(%a) {@[<h4>%a\n return %a;\n@]}" pp_typ
    (snd (m_out cm))
    pp_fun_name (m_name cm) pp_args (m_in cm) (pp_stmt cm) (m_body cm) pp_var
    (m_out cm)
