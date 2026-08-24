(**
  (c) Copyright 2019 Bruno Bentzen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Desc: Checks whether a universe level is lower than or equal to another one,
        whether a universe level is declared in the environment, and whether it 
        is an arbitrary parameter (level variable starting with the prefix '?').
         
 **)

open Ast

(* Checks whether a level or its string variable representation is arbitrary *)

let is_arbitrary = function
  | Var par when String.length par > 0 -> Char.equal par.[0] '?'
  | _ -> false

let is_arbitrary_string par = 
  if String.length par > 0 then par.[0] = '?' else false

(* Universe level evaluation and comparison by flattening on lists of atoms *)

let rec leq k l =
    if k = l then true
    else
      match k, l with
      | Var x, _ when is_arbitrary_string x -> true
      | _, Var y when is_arbitrary_string y -> true

      | Num 0, _ -> true
      | Num n, Num m -> n <= m
      | Num n, Suc k -> leq (Num (n - 1)) k
      | Num n, Max(b1, b2) -> leq (Num n) b1 || leq (Num n) b2
      | Suc k, Suc l -> leq k l
      | Suc k, Num m -> if m = 0 then false else leq k (Num (m - 1))
      | Suc k, Max(b1, b2) -> leq (Suc k) b1 || leq (Suc k) b2

      | Var x, Suc k -> leq (Var x) k
      | Var x, Var y -> x = y
      | Var _, Num _ -> false
      | Var x, Max(k1, k2) -> leq (Var x) k1 || leq (Var x) k2

      | Max(k1, k2), l -> leq k1 l && leq k2 l

      | _ -> false

let rec reduce = function
  | Suc (Num n) -> Num (n + 1)
  | Max (Num n, Num m) -> Num (n + m)
  | Suc n -> Suc (reduce n)
  | Max (Suc n, m) | Max (m, Suc n) -> 
    Suc (reduce (Max (n, m)))
  | Max (n, m) ->
    if leq n m then
      reduce m
    else if leq m n then
      reduce n
    else
      Max (reduce n, reduce m)
  | l -> l

(* Sets all universe levels to be arbitrary placeholders *)

let rec placeholder_level = function
  | Num l -> Num l 
  | Var s -> Var ("?" ^ s)
  | Suc l -> Suc (placeholder_level l)
  | Max (l1, l2) -> Max (placeholder_level l1, placeholder_level l2)

let rec placeholder_levels = function
  | Type lvl -> Type (placeholder_level lvl)
  | Pi (x, l1, l2) -> Pi (x, placeholder_levels l1, placeholder_levels l2)
  | Sigma (x, l1, l2) -> Sigma (x, placeholder_levels l1, placeholder_levels l2)
  | Coe (i, j, l1, l2) -> Coe (placeholder_levels i, placeholder_levels j, placeholder_levels l1, placeholder_levels l2)
  | Hcom (i, j, l1, l2, l3) -> Hcom (placeholder_levels i, placeholder_levels j, placeholder_levels l1, placeholder_levels l2, placeholder_levels l3)
  | App (l1, l2) -> App (placeholder_levels l1, placeholder_levels l2)
  | Pair (l1, l2) -> Pair (placeholder_levels l1, placeholder_levels l2)
  | Fst l -> Fst (placeholder_levels l)
  | Snd l -> Snd (placeholder_levels l)
  | Abort l -> Abort (placeholder_levels l)
  | Pabs (s, l) -> Pabs (s, placeholder_levels l)
  | At (l1, l2) -> At (placeholder_levels l1, placeholder_levels l2)
  | Pathd (l1, l2, l3) -> Pathd (placeholder_levels l1, placeholder_levels l2, placeholder_levels l3)
  | Hole (s, ls) -> Hole (s, List.map placeholder_levels ls)
  | e -> e

(* Returns true when a universe level is less-than-or-equal to another, also returns false if they are incomparable *)

let rec is_declared lvl = function
| Num _ -> Ok ()
| Var name ->
  (* Checks if declaration exists or if it's a parameter level *)
  if List.mem name lvl || Char.equal name.[0] '?' then 
    Ok ()
  else
    Error ("No declaration found for the universe level '" ^ name ^ "'")
| Suc n ->
  begin match is_declared lvl n with
  | Ok _ -> Ok ()
  | Error msg ->
    Error ("Invalid universe level:\n  " ^ Pretty.print_level n ^ "\n" ^ msg)
  end
| Max (n, m) ->
  begin match is_declared lvl n, is_declared lvl m with
  | Ok _, Ok _ -> Ok ()
  | Error msg, _ ->
    Error ("Invalid universe level:\n  " ^ Pretty.print_level n ^ "\n" ^ msg)
  | _, Error msg ->
    Error ("Invalid universe level:\n  " ^ Pretty.print_level m ^ "\n" ^ msg)
  end