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

let generate_ind_pl name num_idx_params ph =
  let rec aux acc ph = function
    | 0 -> Global name, acc
    | n -> 
      let hn = Placeholder.generate_i ph [] in
      let head, phs = aux acc (ph+1) (n - 1) in
      App (head, hn), phs + 1
  in aux 0 ph num_idx_params

(* Infer the motive and indices of a well-applied recursor *)

let rec_motive_idx elaborate global ind_env ctx lvl sl ph vars rec_env ty args = function
  | Global rec_name ->
    begin match Hashtbl.find_opt rec_env rec_name with
    | Some rec_spec ->
      let num_minors = List.length rec_spec.constructors in
      let expected_args = rec_spec.num_indices + 1 + rec_spec.num_params + num_minors + 1 in
      (* Only proceed when the list is fully applied *)
      if (List.length args < expected_args) then
        None
      else
        (* Step 1: proceed only if there are wildcards in the index and motive arguments *)
        let index_is_wild = 
          if rec_spec.num_indices = 0 then false else 
            not (List.compare_length_with 
            (List.filteri (fun i arg -> i < rec_spec.num_indices && 
            Placeholder.is_wild arg) args) 0 = 0) in
        let motive_arg = List.nth args rec_spec.num_indices in
        let motive_is_wild = Placeholder.is_wild motive_arg in
        if index_is_wild || motive_is_wild then
          (* Infer based on the target type by matching parameters and the major argument *)
          let major_arg = List.nth args (expected_args - 1) in
          let rec unpack ty = function
            | 0 -> 
              Expr.fullsubst 0 major_arg (Local 0) true ty
            | n -> let param_arg = List.nth args (rec_spec.num_indices + 1 + n) in
              Expr.fullsubst 0 param_arg (Local n) true (unpack ty (n - 1))
          in
          (* Appends 'dom_ty_arg ->' to the motive for each extra arguments *)
          let num_extra_args = List.length args - expected_args in
          let rec append_ty_extra ty = function
            | 0 -> ty
            | n -> let extra_arg = List.nth args (expected_args + n - 1) in
              let h1 = Placeholder.generate_m ph [] in
              begin match elaborate global ind_env ctx lvl sl h1 ph vars extra_arg with
              | Ok (_, extra_arg_ty, _) -> 
                Pi("v?", extra_arg_ty, Expr.shift 1 0 (append_ty_extra ty (n - 1)))
              | _ -> (* this might happen if the extra argument is another recursor *)
                Pi("v?", Placeholder.generate_fm (ph + n) [], Expr.shift 1 0 (append_ty_extra ty (n - 1))) 
              end
          in
          (* Close motive with abstractions and rebuild the application with the result *)
          let ty' = append_ty_extra (unpack ty rec_spec.num_params) num_extra_args in
          let infer_motive = make_motive (rec_spec.num_params + 1) ty' in
          (* Step 2: elaborate major argument to infer indices *)
          let infer_index =
            let num_idx = rec_spec.num_indices in
            let num_params = rec_spec.num_params in (* Clean this up *)
            let name = rec_spec.ind_name in
            let ph = num_extra_args + ph in (* ensures uniqueness *)
            let h1, ph = generate_ind_pl name (num_idx + num_params) ph in
            begin match elaborate global ind_env ctx lvl sl h1 ph vars major_arg with
            | Ok (_, xty, _) ->
              let _, ind_args = Eval.break_args [] xty in
              let num_args = List.length ind_args in
              if num_args < rec_spec.num_params + rec_spec.num_indices then 
                None
              else
                let idx_args = List.filteri (fun i _ -> i < rec_spec.num_indices) ind_args in
                Some idx_args
            | _ -> None
            end
          in
          (* Step 3: rebuild the application with the inferred motive and indices *)
          let args' = List.mapi (fun i arg -> 
            if i < rec_spec.num_indices && Placeholder.is_wild arg then
              match infer_index with
              | Some idx_args -> List.nth idx_args i
              | None -> if Placeholder.is_wild arg then Placeholder.generate_fi (ph + i) [] else arg
            else
            if i = rec_spec.num_indices && motive_is_wild then infer_motive else arg) args 
          in
          Some (Eval.build_app (Global rec_name) args')
        else None
    | _ -> None
    end
  | _ -> None

(* Infer the indices of a constructor *)

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