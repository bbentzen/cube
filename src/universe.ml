(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Checks whether a universe level is lower than or equal to another one
         
 **)

open Ast

(* Returns true when a universe level is less-than-or-equal to another, also returns false if they are incomparable *)

let rec leq = function
  | Num 0, _ -> 
    true

  | Num n, Num m -> 
    n <= m

  | Var n, Var m -> 
    n = m

  | Max (n, n'), Max (m, m') -> 
    leq (Max (n, n'), m) || leq (Max (n, n'), m')

  | Max (n, n'), m ->
    leq (n, m) && leq (n', m)

  | n, Max (m, m') ->
    leq (n, m) || leq (n, m')

  | Suc n, Suc m -> 
    leq (n, m)
  
  | Num n, Suc m -> 
    leq (Num (n-1), m)

  | n, Suc m -> 
    leq (n, m)

  | Suc _, _ | Num _, Var _ | Var _, Num _ -> 
    false

let rec reduce = function
  | Suc n -> 
    Suc (fst (reduce n)), snd (reduce n)

  | Max (Suc n, m) | Max (m, Suc n) -> 
    Suc (fst (reduce (Max (n, m)))), true

  | Max (n, m) ->
    if leq(n, m) then
      m, true
    else if leq(m, n) then
      n, true
    else
      Max (fst (reduce n), fst (reduce m)),
      snd (reduce n) || snd (reduce m)
    
  | l -> l, false

let rec eval e =
  match reduce e with
  | e', b ->
    if b then 
      eval (e')
    else 
      e'

let rec decl lvl = function
| Num _ -> Ok ()
| Var n -> 
  if List.mem n lvl then 
    Ok ()
  else
    Error ("No declaration found for the universe level '" ^ n ^ "'")
| Suc n ->
  begin
    match decl lvl n with
    | Ok _ -> Ok ()
    | Error msg ->
      Error ("Invalid universe level:\n  " ^ Pretty.print_level n ^ "\n" ^ msg)
  end
| Max (n, m) ->
  begin
    match decl lvl n, decl lvl m with
    | Ok _, Ok _ -> Ok ()
    | Error msg, _ ->
      Error ("Invalid universe level:\n  " ^ Pretty.print_level n ^ "\n" ^ msg)
    | _, Error msg ->
      Error ("Invalid universe level:\n  " ^ Pretty.print_level m ^ "\n" ^ msg)
  end

(* Renames universe variables into hole names *)

let rec to_hole = function
  | Num l -> Num l 
  | Var s -> Var ("?" ^ s)
  | Suc l -> Suc (to_hole l)
  | Max (l1, l2) -> Max (to_hole l1, to_hole l2)

let level_is_arbitrary par =
  Char.equal par.[0] '?'