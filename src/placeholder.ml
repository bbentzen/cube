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

(* Zonks an expression with the solved metavariables *)

let rec solve env = function
  | Meta n -> 
    begin match Hashtbl.find_opt Data.meta_store n with
    | Some stored ->
      (* Close any open variables the solved meta might contain *)
      let rec bind count e = function
        | [] -> e
        | x :: env -> bind (count + 1) (Expr.close_var count x e) env 
      in
      bind 0 stored.solution env
    | None -> Meta n
    end
  | Coe (i, j, e1, e2) ->
    Coe (solve env i, solve env j, solve env e1, solve env e2)
  | Hcom (i, j, e, e1, e2) ->
    Hcom (solve env i, solve env j, solve env e, solve env e1, solve env e2)
  | Lam (x, e) -> Lam (x, solve (x :: env) e)
  | Pabs (x, e) -> Pabs (x, solve (x :: env) e)
  | App (e1, e2) -> App (solve env e1, solve env e2)
  | Pi (x, e1, e2) -> Pi (x, solve env e1, solve env e2)
  | Abort e -> Abort (solve env e)
  | At (e1, e2) -> At (solve env e1, solve env e2)
  | Pathd (e, e1, e2) ->
    Pathd (solve env e, solve env e1, solve env e2)
  | Local _ | Global _ | Int _ | I1 _ | I0 _ | Void _ | Type _ | Wild _ | Subgoal _ as e -> e

(* Assigns unique positive metas to negative metas *)

let rec unique = function
  | Meta _ -> generate ()
  | Coe (i, j, e1, e2) -> Coe (unique i, unique j, unique e1, unique e2)
  | Hcom (i, j, e, e1, e2) ->
    Hcom (unique i, unique j, unique e, unique e1, unique e2)
  | Lam (x, e) -> Lam (x, unique e)
  | App (e1, e2) -> App (unique e1, unique e2)
  | Pi (x, e1, e2) -> Pi (x, unique e1, unique e2)
  | Abort e -> Abort (unique e)
  | Pabs (x, e) -> Pabs (x, unique e)
  | At (e1, e2) -> At (unique e1, unique e2)
  | Pathd (e, e1, e2) -> Pathd (unique e, unique e1, unique e2)
  | e -> e