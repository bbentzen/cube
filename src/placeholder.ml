(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Operations involving placeholders
 **)

open Core_ast

(* Generates a placeholder *)

let generate num_holes l = 
  Hole (string_of_int (num_holes + 1), l)

(* Determines whether an expression is or has a placeholder/underscore *)

let is = function
  | Hole _ | Wild _ -> true
  | _ -> false

(* Tail-recursive recursion with stack for placeholder tracking  *)

let has_placeholder term =
  let rec aux stack =
    match stack with
    | [] -> false
    | x :: rest ->
      match x with
      | Hole _ -> true

      | Abs (_, e) | Pabs (_, e)
      | Fst e | Snd e | Abort e ->
          aux (e :: rest)

      | Pi (_, e1, e2) | Sigma (_, e1, e2)
      | App (e1, e2) | Pair (e1, e2) | At (e1, e2) ->
          aux (e1 :: e2 :: rest)

      | Pathd (e, e1, e2) | Hfill (e, e1, e2) ->
          aux (e :: e1 :: e2 :: rest)

      | Coe (i, j, e1, e2) ->
          aux (i :: j :: e1 :: e2 :: rest)

      | _ -> aux rest
  in
  aux [term]

(* Determines whether an expression has placeholders or underscores *)

let has term =
  let rec aux stack =
    match stack with
    | [] -> false
    | x :: rest ->
      match x with
       Wild _ | Hole _ -> true

      | Abs (_, e) | Pabs (_, e)
      | Fst e | Snd e | Abort e ->
          aux (e :: rest)

      | Pi (_, e1, e2) | Sigma (_, e1, e2)
      | App (e1, e2) | Pair (e1, e2) | At (e1, e2) ->
          aux (e1 :: e2 :: rest)

      | Pathd (e, e1, e2) | Hfill (e, e1, e2) ->
          aux (e :: e1 :: e2 :: rest)

      | Coe (i, j, e1, e2) ->
          aux (i :: j :: e1 :: e2 :: rest)

      | _ -> aux rest
  in
  aux [term]