(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Checks whether a given context is well-formed
 **)

open Basis
open Context
open Eval

let check global ctx lvl =
  let rec helper l = 
    match l with
  | [] -> Ok []
  | (x, ty, b) :: ctx' ->
    begin match Env.unfold_all global 0 ty with
    | Ok ty' ->
      begin match Type.check global ctx' lvl ty', helper ctx' with
      | Ok elab, Ok ctx'' -> 
        if Env.is_declared x global then
          Error ("Naming conflict with the identifier '" ^ x ^ 
            "'\nIt occurs as a definition/theorem name but is declared as a local variable")
        else
          Ok ((x, eval (fst elab), b) :: ctx'')
      | Error msg, _ -> 
        Error ("The specified context is invalid: " ^ msg)
      | _ , Error msg -> Error msg
      end
    | Error msg ->
      Error ("The specified context is invalid: " ^ msg)
    end
  in
  helper (List.rev ctx)

let check_with_universe global ctx lvl =
  let rec helper l = 
    match l with
  | [] -> Ok ([], [])
  | (x, ty, b) :: ctx' ->
    begin match Env.unfold_all global 0 ty with
    | Ok ty' ->
      begin match Type.check global ctx' lvl ty', helper ctx' with
      | Ok (ty', univ), Ok (ctx1, ctx2) -> 
        if Env.is_declared x global then
          Error ("Naming conflict with the identifier '" ^ x ^ 
            "'\nIt occurs as a definition/theorem name but is declared as a local variable")
        else
          Ok (((x, eval ty', b) :: ctx1), ((x, eval univ, b) :: ctx2))
      | Error msg, _ -> 
        Error ("The specified context is invalid: " ^ msg)
      | _ , Error msg -> Error msg
      end
    | Error msg ->
      Error ("The specified context is invalid: " ^ msg)
    end
  in
  helper (List.rev ctx)