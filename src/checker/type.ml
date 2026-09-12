(**
  (c) Copyright 2019 Bruno Bentzen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Desc: Checks whether an expression is a type
        Allows for placeholders to stand for types.
 **)

open Basis
open Ast
open Eval

let check global ind_env ctx lvl ty =
  match ty with
  | Meta _ -> Ok (Meta 0, ty)
  | _ ->
    let ty' = eval ind_env ty in
    Placeholder.restore 0;
    let elab = Elab.elaborate global ind_env ctx lvl ([], []) (Meta 0) 1 ty' in
    match elab with
    | Ok (ty', tTy, _) ->
      begin
        match tTy with
        | Type _ ->
          Ok (ty', tTy)
        | Meta _ -> (* Meta _ has been added for tests *)
          Ok (ty', tTy)
        | _ -> 
          Error ("Failed to prove that \n  " ^ Pretty.printf ty' ^ "\nis a type")
      end
    | Error (_, msg) -> 
      Error msg