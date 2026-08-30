(**
  (c) Copyright 2019 Bruno Bentzen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
 
  Desc: This file contains basic operations involving placeholders. This
        includes generating placeholders, checking whether an expression is a placeholder,
        and checking whether an expression has placeholders.
 **)

open Ast

(* Generates a placeholder *)

let generate num_holes l = 
  Hole (string_of_int (num_holes + 1), l)

(* Determines whether an expression is or has a placeholder/underscore *)

let is = function
| Hole _ | Wild _ -> true
    | _ -> false

(* Tail-recursive recursion with stack for placeholder tracking  *)

let has_placeholder term =
  let rec helper stack =
    match stack with
    | [] -> false
    | x :: rest ->
      match x with
      | Hole _ -> true
      | Lam (_, e) | Pabs (_, e)
      | Abort e ->
          helper (e :: rest)
      | Pi (_, e1, e2) | App (e1, e2) | At (e1, e2) ->
          helper (e1 :: e2 :: rest)
      | Pathd (e, e1, e2) ->
          helper (e :: e1 :: e2 :: rest)
      | Hcom (i, j, e, e1, e2) ->
          helper (i :: j :: e :: e1 :: e2 :: rest)
      | Coe (i, j, e1, e2) ->
          helper (i :: j :: e1 :: e2 :: rest)
      | _ -> helper rest
  in
  helper [term]

(* Determines whether an expression has placeholders or underscores *)

let has term =
  let rec helper stack =
    match stack with
    | [] -> false
    | x :: rest ->
      match x with
       Wild _ | Hole _ -> true
      | Lam (_, e) | Pabs (_, e)
      | Abort e ->
          helper (e :: rest)
      | Pi (_, e1, e2) | App (e1, e2) | At (e1, e2) ->
          helper (e1 :: e2 :: rest)
      | Pathd (e, e1, e2) ->
          helper (e :: e1 :: e2 :: rest)
      | Hcom (i, j, e, e1, e2) ->
          helper (i :: j :: e :: e1 :: e2 :: rest)
      | Coe (i, j, e1, e2) ->
          helper (i :: j :: e1 :: e2 :: rest)
      | _ -> helper rest
  in
  helper [term]