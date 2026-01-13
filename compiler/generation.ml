open Extracted.Imp
open Extracted.Semantics
open Extracted.Types
open Format

let pp_return fmt ident = fprintf fmt "ret_%i" ident.binder_id
let pp_ident fmt ident = fprintf fmt "var_%i" ident
let pp_fun_name fmt ident = fprintf fmt "fun_%s" ident

let pp_const fmt c =
  match c with
  | CBool c -> fprintf fmt "%s" (if c then "1" else "0")
  | CInt i -> fprintf fmt "%i" i

let pp_typ fmt typ =
  match typ with
  | TBool -> fprintf fmt "char"
  | TInt -> fprintf fmt "int"

let pp_var fmt v = pp_ident fmt v.binder_id

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
  | Bop_neq -> fprintf fmt "<>"
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
  | _, (Bop_eq | Bop_neq | Bop_le | Bop_lt | Bop_ge | Bop_gt) -> true
  | ( Some
        ( BinaryL (Bop_eq | Bop_neq | Bop_le | Bop_lt | Bop_ge | Bop_gt)
        | BinaryR (Bop_eq | Bop_neq | Bop_le | Bop_lt | Bop_ge | Bop_gt) ),
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

let rec pp_expr parent_op (env : binder list) fmt exp =
  match exp with
  | EConst (_, c) -> fprintf fmt "%a" pp_const c
  | EVar v ->
      if List.mem v env then fprintf fmt "%a" pp_var v
      else fprintf fmt "this->%a" pp_var v
  | EUnop (_, _, op, e) ->
      if needs_paren_unary op parent_op then
        fprintf fmt "@[(%a%a)@]" pp_unop op (pp_expr (Some (Unary op)) env) e
      else fprintf fmt "@[%a%a@]" pp_unop op (pp_expr (Some (Unary op)) env) e
  | EBAnd (e1, e2) ->
      if needs_paren_binary_and parent_op then
        fprintf fmt "(@[%a &&@ %a@])"
          (pp_expr (Some BinaryAndL) env) e1
          (pp_expr (Some BinaryAndR) env) e2
      else
        fprintf fmt "@[<hv2>%a &&@ %a@]"
          (pp_expr (Some BinaryAndL) env) e1
          (pp_expr (Some BinaryAndR) env) e2
  | EBOr (e1, e2) ->
      if needs_paren_binary_or parent_op then
        fprintf fmt "(@[%a ||@ %a@])"
          (pp_expr (Some BinaryOrL) env) e1
          (pp_expr (Some BinaryOrR) env) e2
      else
        fprintf fmt "@[<hv2>%a ||@ %a@]"
          (pp_expr (Some BinaryOrL) env) e1
          (pp_expr (Some BinaryOrR) env) e2
  | EBinop (_, _, _, op, e1, e2) ->
      if needs_paren_binary op parent_op then
        fprintf fmt "(@[%a %a@ %a@])"
          (pp_expr (Some (BinaryL op)) env) e1
          pp_binop op
          (pp_expr (Some (BinaryR op)) env) e2
      else
        fprintf fmt "@[<hv2>%a %a@ %a@]"
          (pp_expr (Some (BinaryL op)) env) e1
          pp_binop op
          (pp_expr (Some (BinaryR op)) env) e2
  | EIfte (_, cond, e1, e2) ->
      if needs_paren_ternary parent_op then
        fprintf fmt "@[<hv>(%a ?@ %a :@ %a)@]" (pp_expr (Some TernaryL) env) cond
          (pp_expr (Some TernaryM) env) e1 (pp_expr (Some TernaryR) env) e2
      else
        fprintf fmt "@[<hv>%a ?@ %a :@ %a@]" (pp_expr (Some TernaryL) env) cond
          (pp_expr (Some TernaryM) env) e1 (pp_expr (Some TernaryR) env) e2

let is_empty_sassign stmt = ignore stmt; false

let get_var_typ (env : binder list) var =
  List.find_opt (fun { binder_id = name; _ } -> name = var.binder_id) env |> Option.map (fun b -> b.binder_ty)

let rec pp_stmt env fmt stmt =
  match stmt with
  | SAssign (b, e) -> begin match get_var_typ env b with
    | Some ty ->
      fprintf fmt "@[<hv2>%a %a =@ %a;@]" pp_typ ty pp_var b
        (pp_expr None env) e
    | None ->
      fprintf fmt "@[<hv2>this->%a =@ %a;@]" pp_var b
        (pp_expr None env) e
    end
  | SSeq (s1, s2) when is_empty_sassign s1 -> pp_stmt env fmt s2
  | SSeq (s1, s2) when is_empty_sassign s2 -> pp_stmt env fmt s1
  | SSeq (s1, s2) -> fprintf fmt "%a@\n%a" (pp_stmt env) s1 (pp_stmt env) s2
  | SNop -> fprintf fmt ""

let pp_arg fmt arg = fprintf fmt "%a %a" pp_typ arg.binder_ty pp_var arg

let pp_args fmt (args : binder list) =
  match args with
  | [] -> ()
  | _ :: _ ->
      fprintf fmt ", @[%a@]"
        (pp_print_list
          ~pp_sep:(fun fmt () -> fprintf fmt ",@ ")
          (fun fmt arg -> fprintf fmt "%a" pp_arg arg))
        args

let pp_struct_typ fmt (args : binder list) =
  pp_print_list
    ~pp_sep:(fun _fmt () -> ())
    (fun fmt b -> fprintf fmt "@\n%a %a;" pp_typ b.binder_ty pp_return b)
    fmt args

let pp_struct_val sname fmt (args : binder list) =
  fprintf fmt "(%s){ @[<hv>%a@] }"
    sname
    (pp_print_list
      ~pp_sep:(fun fmt () -> fprintf fmt ";@ ")
      (fun fmt b -> fprintf fmt ".%a = %a" pp_return b pp_var b)) args

let pp_coq_method fmt (fname, sname, bin, bout, blocals, body) = match bout with
  | [] -> (* Warning, no output! *)
      fprintf fmt "@[@[<v4>void %a(struct %s *this%a) {%a@]@\n}@\n@]"
        pp_fun_name fname
        sname
        pp_args bin
        (pp_stmt blocals) body
  | [m_out] ->
      fprintf fmt "@[@[<v4>%a %a(struct %s *this%a) {%a@\nreturn @[%a@];@]@\n}@\n@]"
        pp_typ m_out.binder_ty
        pp_fun_name fname
        sname
        pp_args bin
        (pp_stmt blocals) body
        pp_var m_out
  | _ :: _ :: _ ->
      let return_name = asprintf "return_%s" fname in
      fprintf fmt "@[@[<v4>struct %s {%a@]@\n};@\n@[<v4>%s %a(struct %s *this%a) {%a@\nreturn @[%a@];@]@\n}@\n@]"
        return_name
        pp_struct_typ bout
        return_name
        pp_fun_name fname
        sname
        pp_args bin
        (pp_stmt blocals) body
        (pp_struct_val return_name) bout

type formatting = { fprintf : 'a. ('a, formatter, unit) format -> 'a }
let pp_coq_method_pair {fprintf} cm =
  let sname = "s_" ^ m_name cm in
  let pp_locals fmt locs =
    pp_print_list ~pp_sep:(fun _ () -> ())
      (fun fmt loc -> Format.fprintf fmt "@\n%a %a;" pp_typ loc.binder_ty pp_var loc)
      fmt locs in
  let locvars = m_in cm @ m_out cm in
  fprintf "@[@[<v4>struct %s {%a@]@\n};@\n@\n%a@\n%a@]"
    sname
    pp_locals (m_locals cm)
    pp_coq_method ("init_" ^ m_name cm, sname, m_in cm, m_out cm, locvars, m_init cm)
    pp_coq_method ("step_" ^ m_name cm, sname, m_in cm, m_out cm, locvars @ m_pre cm, m_step cm)
