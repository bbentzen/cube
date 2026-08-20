(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Checks whether a given context is well-formed
 **)

open Basis
open Context
open Eval

let check global ind_env ind ctx lvl =
  let rec helper l = 
    match l with
  | [] -> Ok []
  | (x, ty, b) :: ctx' ->
    begin match Env.unfold_all global 0 ty with
    | Ok ty' ->
      (* Dumps inductive type data into the context *)
      let ind_ctx = List.map (fun (id, ty) -> (id, ty, true)) ind @ ctx' in
      begin match Type.check global ind_env ind_ctx lvl ty', helper ctx' with
      | Ok elab, Ok ctx'' -> 
        if Env.is_declared x global then
          Error ("Naming conflict with the identifier '" ^ x ^ 
            "'\nIt occurs as a definition/theorem name but is declared as a local variable")
        else
          Ok ((x, eval ind_env (fst elab), b) :: ctx'')
      | Error msg, _ -> 
        Error ("The specified context is invalid: " ^ msg)
      | _ , Error msg -> Error msg
      end
    | Error msg ->
      Error ("The specified context is invalid: " ^ msg)
    end
  in
  helper (List.rev ctx)

let check_with_universe global ind_env ctx lvl =
  let rec helper l = 
    match l with
  | [] -> Ok ([], [])
  | (x, ty, b) :: ctx' ->
    begin match Env.unfold_all global 0 ty with
    | Ok ty' ->
      begin match Type.check global ind_env ctx' lvl ty', helper ctx' with
      | Ok (ty', univ), Ok (ctx1, ctx2) -> 
        if Env.is_declared x global then
          Error ("Naming conflict with the identifier '" ^ x ^ 
            "'\nIt occurs as a definition/theorem name but is declared as a local variable")
        else
          Ok (((x, eval ind_env ty', b) :: ctx1), ((x, eval ind_env univ, b) :: ctx2))
      | Error msg, _ -> 
        Error ("The specified context is invalid: " ^ msg)
      | _ , Error msg -> Error msg
      end
    | Error msg ->
      Error ("The specified context is invalid: " ^ msg)
    end
  in
  helper (List.rev ctx)

let rec placeholder_levels = function
  | [] -> []
  | (x, ty, b) :: ctx' ->
      (x, Core_ast.placeholder_levels ty, b) :: placeholder_levels ctx'