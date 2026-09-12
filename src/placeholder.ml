(**
  (c) Copyright 2019 Bruno Bentzen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
 
  Desc: This file contains basic operations involving placeholders. This
        includes generating placeholders, checking whether an expression is a placeholder,
        and checking whether an expression has placeholders.
 **)

open Ast

(* Generates a placeholder *)

let counter = ref 0

let generate () =
  incr counter; Meta (!counter)

let generate_neg () =
  decr counter;
  Meta (!counter)

let restore n = counter := n

(* Determines whether an expression is a placeholder/underscore *)

let is = function
| Meta _ | Wild _ -> true
    | _ -> false

(* Determines whether an expression is an underscore *)

let is_wild = function
| Wild _ -> true | _ -> false

(* Tail-recursive recursion with stack for placeholder tracking  *)

let has_placeholder term =
  let rec helper stack =
    match stack with
    | [] -> false
    | x :: rest ->
      match x with
      | Meta _ -> true
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

let has_placeholder_name name term =
  let rec helper stack =
    match stack with
    | [] -> false
    | x :: rest ->
      match x with
      | Meta n when n = name -> true
      | Meta _ -> false
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
       Wild _ | Meta _ -> true
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

let rec solve = function
  | Meta n -> 
    begin match Hashtbl.find_opt Data.meta_store n with
    | Some stored ->
      stored.solution
    | None -> Meta n
    end
  | Coe (i, j, e1, e2) ->
    Coe (solve i, solve j, solve e1, solve e2)
  | Hcom (i, j, e, e1, e2) ->
    Hcom (solve i, solve j, solve e, solve e1, solve e2)
  | Lam (x, e) -> Lam (x, solve e)
  | App (e1, e2) -> App (solve e1, solve e2)
  | Pi (x, e1, e2) -> Pi (x, solve e1, solve e2)
  | Abort e -> Abort (solve e)
  | Pabs (x, e) -> Pabs (x, solve e)
  | At (e1, e2) -> At (solve e1, solve e2)
  | Pathd (e, e1, e2) ->
    Pathd (solve e, solve e1, solve e2)
  | Local _ | Global _ | Int _ | I1 _ | I0 _ | Void _ | Type _ | Wild _ | Subgoal _ as e -> e