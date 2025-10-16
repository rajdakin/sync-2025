open Extracted.Imp
open Format

let pretty_printer m = printf "Ok: %s\n" (m_name m)
let pp_ident fmt ident = fprintf fmt "var_%i" ident
let pp_fun_name fmt ident = fprintf fmt "fun_%s" ident

let pp_const fmt c =
  match c with
  | CBool c -> fprintf fmt "%s" (if c then "1" else "0")
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
  | Bop_xor -> fprintf fmt "^"
  | Bop_plus -> fprintf fmt "+"
  | Bop_minus -> fprintf fmt "-"
  | Bop_mult -> fprintf fmt "*"
  | Bop_div -> fprintf fmt "/"
  | Bop_eq -> fprintf fmt "=="
  | Bop_le -> fprintf fmt "<="
  | Bop_lt -> fprintf fmt "<"
  | Bop_ge -> fprintf fmt ">="
  | Bop_gt -> fprintf fmt ">"

type parent_op =
  | Unary of unop
  | BinaryL of binop
  | BinaryR of binop
  | BinaryAndL | BinaryOrL
  | BinaryAndR | BinaryOrR
  | TernaryL
  | TernaryM
  | TernaryR

(* [op] needs to be parenthesized when inside [parent_op] *)
let needs_paren_unary op parent_op =
  match parent_op, op with
  | None, _ -> false
  | _, Uop_not -> true
  | _, Uop_neg -> true

let needs_paren_binary_and parent_op =
  match parent_op with
  | None -> false
  | Some (BinaryAndL | BinaryAndR) -> false
  | Some _ -> true

let needs_paren_binary_or parent_op =
  match parent_op with
  | None -> false
  | Some (BinaryOrL | BinaryOrR) -> false
  | Some _ -> true

let needs_paren_binary op parent_op =
  match parent_op, op with
  | None, _ -> false
  (* Boolean operators *)
  | Some (BinaryAndL | BinaryOrL | BinaryAndR | BinaryOrR), _ -> true
  (* Xor is not a boolean operator... *)
  (* Comparisons operators *)
  | _, (Bop_eq | Bop_le | Bop_lt | Bop_ge | Bop_gt) -> true
  | ( Some
        ( BinaryL (Bop_eq | Bop_le | Bop_lt | Bop_ge | Bop_gt)
        | BinaryR (Bop_eq | Bop_le | Bop_lt | Bop_ge | Bop_gt) ),
      _ ) ->
      false
  (* Arithmetic operators *)
  | Some (BinaryL Bop_xor | BinaryR Bop_xor), Bop_xor -> false
  | _, Bop_xor -> true
  | ( Some (BinaryL (Bop_plus | Bop_minus) | BinaryR Bop_plus),
      (Bop_plus | Bop_minus) ) ->
      false
  | _, (Bop_plus | Bop_minus) -> true
  | ( Some
        ( BinaryL (Bop_mult | Bop_div | Bop_plus | Bop_minus)
        | BinaryR (Bop_mult | Bop_plus | Bop_minus) ),
      (Bop_mult | Bop_div) ) ->
      false
  | _, (Bop_mult | Bop_div) -> true

let needs_paren_ternary _parent_op = true

let rec pp_expr parent_op fmt exp =
  match exp with
  | EConst (_, c) -> fprintf fmt "%a" pp_const c
  | EInput _ -> ()
  | EVar v -> fprintf fmt "%a" pp_var v
  | EUnop (_, _, op, e) ->
      if needs_paren_unary op parent_op then
        fprintf fmt "@[(%a%a)@]" pp_unop op (pp_expr (Some (Unary op))) e
      else fprintf fmt "@[%a%a@]" pp_unop op (pp_expr (Some (Unary op))) e
  | EBAnd (e1, e2) ->
      if needs_paren_binary_and parent_op then
        fprintf fmt "(@[%a &&@ %a@])"
          (pp_expr (Some BinaryAndL)) e1
          (pp_expr (Some BinaryAndR)) e2
      else
        fprintf fmt "@[<hv2>%a &&@ %a@]"
          (pp_expr (Some BinaryAndL)) e1
          (pp_expr (Some BinaryAndR)) e2
  | EBOr (e1, e2) ->
      if needs_paren_binary_or parent_op then
        fprintf fmt "(@[%a ||@ %a@])"
          (pp_expr (Some BinaryOrL)) e1
          (pp_expr (Some BinaryOrR)) e2
      else
        fprintf fmt "@[<hv2>%a ||@ %a@]"
          (pp_expr (Some BinaryOrL)) e1
          (pp_expr (Some BinaryOrR)) e2
  | EBinop (_, _, _, op, e1, e2) ->
      if needs_paren_binary op parent_op then
        fprintf fmt "(@[%a %a@ %a@])"
          (pp_expr (Some (BinaryL op))) e1
          pp_binop op
          (pp_expr (Some (BinaryR op))) e2
      else
        fprintf fmt "@[<hv2>%a %a@ %a@]"
          (pp_expr (Some (BinaryL op))) e1
          pp_binop op
          (pp_expr (Some (BinaryR op))) e2
  | EIfte (_, cond, e1, e2) ->
      if needs_paren_ternary parent_op then
        fprintf fmt "@[<hv>(%a ?@ %a :@ %a)@]" (pp_expr (Some TernaryL)) cond
          (pp_expr (Some TernaryM)) e1 (pp_expr (Some TernaryR)) e2
      else
        fprintf fmt "@[<hv>%a ?@ %a :@ %a@]" (pp_expr (Some TernaryL)) cond
          (pp_expr (Some TernaryM)) e1 (pp_expr (Some TernaryR)) e2

let is_empty_sassign stmt =
  match stmt with SAssign (_, EInput _) -> true | _ -> false

let get_var_typ var env =
  snd (List.find (fun (name, _) -> name = var) (m_vars env))

let rec pp_stmt env fmt stmt =
  match stmt with
  | SAssign (_, EInput _) -> ()
  | SAssign ((x, _), e) ->
      fprintf fmt "@[<hv2>%a %a =@ %a;@]" pp_typ (get_var_typ x env) pp_ident x
        (pp_expr None) e
  | SSeq (s1, s2) when is_empty_sassign s1 -> pp_stmt env fmt s2
  | SSeq (s1, s2) when is_empty_sassign s2 -> pp_stmt env fmt s1
  | SSeq (s1, s2) -> fprintf fmt "%a@\n%a" (pp_stmt env) s1 (pp_stmt env) s2
  | SNop -> fprintf fmt ""

let pp_binder fmt binder = fprintf fmt "%a" pp_ident (fst binder)
let pp_arg fmt arg = fprintf fmt "%a %a" pp_typ (snd arg) pp_binder arg

let pp_args fmt (args : binder list) =
  Format.pp_print_list
    ~pp_sep:(fun fmt () -> fprintf fmt ",@ ")
    (fun fmt arg -> fprintf fmt "%a" pp_arg arg)
    fmt args

let pp_coq_method cm =
  printf "@[@[<v4>%a %a(@[%a@]) {%a@\nreturn %a;@]@\n}@\n@]" pp_typ
    (snd (m_out cm))
    pp_fun_name (m_name cm) pp_args (m_in cm) (pp_stmt cm) (m_body cm) pp_var
    (m_out cm)
