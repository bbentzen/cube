(**
  (c) Copyright 2026 Bruno Bentzen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Desc: Implements a strict positivity checker for inductive types 
        and generates the corresponding elimination rules.
 **)

(* TODO: coercion effect, improve how inductive types, constructors, 
elims are described as variables and printed in the ctx *)

open Basis
open Ast
open Data

let rec occurs_name id l = function
  | Global t -> t = id 
  | Lam (x, e) | Pabs (x, e) -> x = id || occurs_name x l e
  | Pi (x, e1, e2) | Sigma (x, e1, e2) -> x = id || occurs_name x l e1 || occurs_name x l e2
  | Local index -> 
    begin match List.nth_opt l index with
    | Some h -> h = id | None -> false
    end
  | Int _ | I1 _ | I0 _ | Void _ | Type _ | Wild _ | Subgoal _ -> false
  | Hole (_, l') -> List.exists (occurs_name id l) l'
  | Coe (i, j, e1, e2) -> occurs_name id l i || occurs_name id l j || occurs_name id l e1 || occurs_name id l e2
  | Hcom (i, j, e, e1, e2) -> occurs_name id l i || occurs_name id l j || occurs_name id l e || occurs_name id l e1 || occurs_name id l e2
  | App (e1, e2) | Pair (e1, e2) | At (e1, e2) -> occurs_name id l e1 || occurs_name id l e2
  | Fst e | Snd e | Abort e -> occurs_name id l e
  | Pathd (e, e1, e2) ->
    occurs_name id l e || occurs_name id l e1 || occurs_name id l e2

(* Returns the head symbol of an application tree *)

let rec head_symbol = function
  | Global x -> Some x
  | App (e1, _) -> head_symbol e1
  | _ -> None

(* Checks that 'ty' appears only strictly positively in a constructor argument *)

let rec strictly_positive_arg ty = function
  | Pi (x, dom, cod) ->
      not (occurs_name ty [x] dom) && strictly_positive_arg ty cod
  | expr ->
      (* If ind_name occurs in the target of an argument, it must be the head symbol *)
      if occurs_name ty [] expr then
        match head_symbol expr with
        | Some x -> x = ty
        | None -> false
      else true

(* Validates strict positivity across an entire constructor type signature *)

let rec strictly_positive ind_name = function
  | Pi (_, arg_ty, rest_ty) ->
      strictly_positive_arg ind_name arg_ty &&
      strictly_positive ind_name rest_ty
  | target_ty ->
      (* The final return type of the constructor must target ind_name *)
      match head_symbol target_ty with
      | Some x -> x = ind_name
      | None -> false

(* Loads inductive types, constructors, and eliminators to top of the context *)
let add ind ctx =
ctx @ (List.map (fun (id, ty) -> (id, ty, true)) ind)

(* Opens a type family with abstractions matching its context *)

let rec abs_ctx_args e = function
| [] -> e
| ((x, ty, _) :: ctx) -> Pi (x, ty, Expr.close_var 0 x (abs_ctx_args e ctx))

let parametrize_constructor_ty c_ty ctx = 
  abs_ctx_args c_ty ctx

(* Closes a type family with applications matching its context *)

let rec app_ctx_args ind_name = function
| [] -> Global ind_name
| ((x, _, _) :: ctx) -> App (app_ctx_args ind_name ctx, Global x)

(* Closes a function with applications matching its arity *)

let app_constr_args c_expr = 
  let rec helper m c_expr = function 
  | 0 -> c_expr
  | n -> App (helper m c_expr (n - 1), Local (m - n)) in 
fun arity -> helper arity c_expr arity

(* Opens a type with abstractions matching a type family and counts its arity *)

let rec abs_par_args e = function
  | Pi (x, dom, cod) ->
    if x = "v?" then
      Pi ((Expr.create_fresh [e; dom; cod] 1).(0), dom, 
      Expr.close_var 0 x (abs_par_args e cod)) 
    else
      Pi (x, dom, abs_par_args e cod)
  | _ -> e 

let ar_type_fam = 
  let rec count ar = function
  | Pi (_, _, cod) -> count (ar+1) cod
  | _ -> ar 
in count 0

(* Creates fresh constructor variables matching the name of the inductive type *)

let create_fresh_cons ind_name es vars n =
  let var = String.sub ind_name 0 1 in
  let rec add_prime var = function
    | 0 -> var
    | i -> (add_prime var (i - 1)) ^ "'" in
  let rec helper i e n =
    if Expr.occurs_name (var) (add_prime var i) e then
      helper (i+1) e n
    else if n > 0 then
      add_prime var i
    else
      add_prime var 0
  in  (* not free_var *)
  helper vars (Expr.list_to_expr es) n

(* Helper to extract parameters from type of constructor *)

let rec find_params_cons ind_fam expr = function
  | Pi (_, _, cod) ->
    find_params_cons ind_fam expr cod
  | cod ->
    Expr.fullsubst 0 ind_fam expr true cod

(* Helper to extract induction hypotheses for recursive arguments in a constructor *)

let rec build_ihs ind_name ind_ty motive_name ar vars ctx c_name = function
  | Pi (_, arg_ty, rest) ->
      let var = create_fresh_cons ind_name [arg_ty; rest] vars 1 in
      let ih_wrap ar = build_ihs ind_name ind_ty motive_name ar (vars+1) ctx c_name rest in
      if occurs_name ind_name [] arg_ty then (* IH for recursive occurrences *)
        let ih_ty = App (Global motive_name, Local 0) in 
        Pi (var, arg_ty, Pi (var ^ "_ih", ih_ty, Expr.shift 0 1 (ih_wrap (ar + 1))))
      else
        Pi (var, arg_ty, (ih_wrap (ar + 1)))
  | c_ty ->
    match ind_ty with
    | Pi (_, _, _) ->
      (* If type has parameters we infer it from the constructor's type and prefix it to the constructor *)
      let ind_fam = app_ctx_args ind_name ctx in
      let head = find_params_cons ind_fam (Global motive_name) c_ty in
      App (head, app_constr_args (app_ctx_args c_name ctx) ar )
    | _ ->
      (* Otherwise we apply the motive to all constructor arguments *)
      App (Global motive_name, app_constr_args (app_ctx_args c_name ctx) ar )

(* Synthesizes the full recursor type for an inductive definition *)

let generate_recursor ind_name ind_ty constrs ctx ctx_rev = (*ind_ty *)
  let motive_name = "C" in
  let var = create_fresh_cons ind_name [] 1 0 in (* not sure if this should be empty*)
  
  (* Applies parameters and context arguments *)
  let motive_dom = app_constr_args (app_ctx_args ind_name ctx) (ar_type_fam ind_ty) in
  let motive_ty = Pi (var, motive_dom, Type (Var "?_")) in

  let rec add_minor_premises = function
    | [] ->
      (* Generates target type with parameters *)
      let abs_params x = abs_par_args x ind_ty in
      let app_params x = Expr.shift 0 1 (app_constr_args x (ar_type_fam ind_ty)) in
      abs_params (Pi (var, motive_dom, App (app_params (Global motive_name), Local 0))) 
    | (c_name, c_ty) :: rest ->
      let minor_ty = build_ihs ind_name ind_ty motive_name 0 0 ctx c_name c_ty in
      Pi ("c_" ^ c_name, minor_ty, add_minor_premises rest)
  in
  (* Prefix the recursor with the index of the inductive type and its parameters *)
  let abs_params x = abs_par_args x ind_ty in
  let abs_indices x = abs_ctx_args x ctx_rev in
  abs_indices (Pi (motive_name, abs_params motive_ty, Expr.close_var 0 motive_name (add_minor_premises constrs)))

(* Generates type family *)

let generate_type_family id ctx ty =
  snd (snd (Context.Env.function_of_def id ctx (Global id, ty) 0))

(* Extracts universe level l if expr is Type l *)

  let rec extract_universe_level = function
  | Type lvl -> Some lvl
  | Pi (_, _, cod) -> extract_universe_level cod
  | _ -> None

(* Checks that all parameter and constructor argument levels <= target level *)

let check_universe_levels ctx_univ constrs_univs target_lvl =
  let rec helper_ctx target_lvl = function
  | [] -> true
  | (_, univ, _) :: ctx_univ ->
    match extract_universe_level univ with
      | Some lvl ->
          Level.leq lvl target_lvl && 
          helper_ctx target_lvl ctx_univ
      | None -> false
  in
  let rec helper_constrs target_lvl = function
  | [] -> true
  | (_, c_univ) :: constrs_univs ->
    match extract_universe_level c_univ with
      | Some lvl ->
          Level.leq lvl target_lvl && 
          helper_constrs target_lvl constrs_univs
      | None -> false 
  in 
  helper_ctx target_lvl ctx_univ &&
  helper_constrs target_lvl constrs_univs

(* Prints the inductive types with their constructors *)

let print ctx = 
  let rec printrev = function
    | [] -> "" 
    | (id, ty) :: ctx -> 
      " " ^ id ^ " : " ^ Pretty.printf ty ^ "\n" ^ printrev ctx
  in
  printrev (List.rev ctx)

(* Global registry of evaluated inductive definitions *)

let rec_name id_name = id_name ^ "rec"

(* Useful for testing purposes *)

let print_spec id ind = 
  "\nType: " ^ id ^ "\nNum_indices: " ^ string_of_int ind.num_indices ^ "\nNum_params: " ^ string_of_int ind.num_params ^ "\nConstructors: " ^
  String.concat "" (List.map (fun c -> "\nConstructor name: " ^ c.c_name ^ "\nConstructor Num_args: " ^ string_of_int c.c_num_args ^ "\nConstructor Rec_args: " ^ String.concat "" (List.map string_of_bool c.c_rec_args)) ind.constructors)

let find_print id ind_env =
  match Hashtbl.find_opt ind_env id with
            | Some rec_spec ->
              print_spec id rec_spec
            | None -> "Inductive type not found in environment"