(**
  (c) Copyright 2026 Bruno Bentzen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  
  Desc: Infers the motive of a recursor when it is applied to a placeholder 
        by checking the target type and the parameters and major arguments of the recursor. 
 **)

open Basis
open Ast
open Data

let make_motive n ty = 
  let vars = Expr.create_fresh [ty] (1 + n) in
  let rec helper ty = function
  | 0 -> ty
  | n -> Lam (vars.(n-1), helper (Expr.shift 1 0 ty) (n - 1)) 
  in helper ty n

(* Infer the motive of a well-applied recursor *)

let try_infer_motive rec_env ty args = function
  | Global rec_name ->
    begin match Hashtbl.find_opt rec_env rec_name with
    | Some rec_spec -> 
      let num_minors = List.length rec_spec.constructors in
      let expected_args = rec_spec.num_indices + 1 + rec_spec.num_params + num_minors + 1 in
  
      if List.length args < expected_args then
        None (* Not fully applied yet *)
      else
        let motive_arg = List.nth args rec_spec.num_indices in
        if Placeholder.is motive_arg then
          (* Infer based on the target type by matching parameters and the major argument *)
          let rec unpack ty = function
            | 0 -> let major_arg = List.nth args (expected_args - 1) in
              Expr.fullsubst 0 major_arg (Local 0) true ty
            | n -> let param_arg = List.nth args (rec_spec.num_indices + 1 + n) in
              Expr.fullsubst 0 param_arg (Local n) true (unpack ty (n - 1))
          in
          let ty' = unpack ty rec_spec.num_params in
          (* Close motive with abstractions and rebuild the application with the result *)
          let infer_motive = make_motive (rec_spec.num_params + 1) ty' in
          let args' = List.mapi (fun i arg -> if i = rec_spec.num_indices then infer_motive else arg) args in
          Some (Eval.build_app (Global rec_name) args')
        else None
    | _ -> None
    end
  | _ -> None

let constr_indices cons_env ty args = function
  | Global cons_name ->
    let _, ty_args = Eval.break_args [] ty in
    begin match Hashtbl.find_opt cons_env cons_name with
    | Some cons_spec -> 
      let expected_args = cons_spec.num_indices in
      if List.length ty_args < expected_args || List.length args < expected_args then
        None
      else
        let infer_index i = List.nth ty_args i in
        let args' = List.mapi (fun i arg -> if i < expected_args && Placeholder.is (List.nth args i) then infer_index i else arg) args in
        if args = args' then (* not super efficient but that'd do for now *)
          None 
        else
          Some (Eval.build_app (Global cons_name) args')
    | _ -> None
    end
  | _ -> None