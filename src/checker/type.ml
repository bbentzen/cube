(**
  (c) Copyright 2019 Bruno Bentzen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Desc: Checks whether an expression is a type
        Allows for placeholders to stand for types.
 **)

open Basis
open Ast
open Eval

let check global ctx lvl ty =
  match ty with
  | Meta _ -> Ok (Meta 0, ty)
  | _ ->
    (* Imported implicit-argument templates must be instantiated in targets
       too; distinct uses of a definition must not share its holes. *)
    let ty' = eval (Placeholder.unique ty) in
    Placeholder.restore 0;
    let sort = Placeholder.generate () in
    let elab = Elab.elaborate global ctx lvl ([], []) sort 1 [] ty' in
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