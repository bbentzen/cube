(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Checks whether a universe level is lower than or equal to another one
         
 **)



(* Returns true when a universe level is less-than-or-equal to another, also returns false if they are incomparable *)


let rec decl2 lvl = function
| Core_ast.Num _ -> Ok ()
| Core_ast.Var name ->
  (* Checks if declaration exists or if it's a parameter level *)
  if List.mem name lvl || Char.equal name.[0] '?' then 
    Ok ()
  else
    Error ("No declaration found for the universe level '" ^ name ^ "'")
| Core_ast.Suc n ->
  begin match decl2 lvl n with
  | Ok _ -> Ok ()
  | Error msg ->
    Error ("Invalid universe level:\n  " ^ Pretty.print_level n ^ "\n" ^ msg)
  end
| Core_ast.Max (n, m) ->
  begin match decl2 lvl n, decl2 lvl m with
  | Ok _, Ok _ -> Ok ()
  | Error msg, _ ->
    Error ("Invalid universe level:\n  " ^ Pretty.print_level n ^ "\n" ^ msg)
  | _, Error msg ->
    Error ("Invalid universe level:\n  " ^ Pretty.print_level m ^ "\n" ^ msg)
  end

(* Renames universe variables into hole names *)

(* let rec to_hole = function
  | RNum l -> RNum l 
  | RVar s -> RVar ("?" ^ s)
  | RSuc l -> RSuc (to_hole l)
  | RMax (l1, l2) -> RMax (to_hole l1, to_hole l2) *)

let level_is_arbitrary par =
  Char.equal par.[0] '?'

open Core_ast

let arbitrary_level = function
  | Var par -> Char.equal par.[0] '?'
  | _ -> false