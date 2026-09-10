(**
  (c) Copyright 2019 Bruno Bentzen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  
  Desc: Typechecked definitions are appended to an "environment", a list of
        identifiers with their proof term and their type. Identifiers are used as 
        global variables in the internal de Bruijn representation of terms.
        This file handles operations on this environment list.
 **)

open Basis
open Ast
open Expr

(* Determines whether a string is declared in the environment *)

let is_declared x env =
  let rec helper x = function
    | [] -> false
    | (id,_) :: env -> 
      if x = id then 
        true
      else 
        helper x env
  in
  helper x (List.rev env)

(* Generates a triple id * term * type from a successfully elaborated triple id * ctx * elab *)

let function_of_def id ctx (e, ty) hole =
  let rec helper h' = function
    | [] -> e, ty
    | (x, ty, true) :: ctx ->
      let e', ty' = helper h' ctx in
      Lam (x, close_var 0 x e'), 
      Pi (x, ty, close_var 0 x ty')
    | (x, _, false) :: ctx ->
      let e', ty' = helper (h'+1) ctx in
      let h = Placeholder.generate [] in
      Global.subst_global 0 h x e', 
      Global.subst_global 0 h x ty' 
  in
  id, helper hole ctx

let rec check_def_id id = function
  | [] -> 
    Error ("No definition or theorem found for the identifier '" ^ id ^ "'") 
  | (id', body) :: env -> 
    if id = id'
    then Ok body
    else check_def_id id env

(* Appends a triple id * term * type to the env context *)

let add env id ctx elab =
  match check_def_id id env with
  | Ok _ -> env
  | Error _ -> function_of_def id ctx elab 0 :: env

(* Returns the body of a definition when given a declared env constant *)

let rec unfold id = function
  | [] -> 
    Error ("No declaration found for identifier '" ^ id ^ "'")
  | (id', (body , ty)) :: env -> 
    if id = id' then 
      Ok (body, ty)
    else 
      unfold id env

(* Uniformly lifts all indices of implicit arguments in a env variable *)

let rec lift n = function
  | Wild m ->
    Wild (m+n)
  | Coe (i, j, e1, e2) -> 
    Coe (lift n i, lift n j, 
    lift n e1, lift n e2)
  | Hcom (i, j, e, e1, e2) -> 
    Hcom (lift n i, lift n j, lift n e, lift n e1, lift n e2)
  | Lam (y, e) -> 
    Lam (y, lift n e)
  | App (e1, e2) -> App (lift n e1, lift n e2)
  | Pi (y, e1, e2) -> 
    Pi (y, lift n e1, lift n e2)
  | Abort e -> Abort (lift n e)
  | Pabs (y, e) -> 
    Pabs (y, lift n e)
  | At (e1, e2) -> 
    At (lift n e1, lift n e2)
  | Pathd (e, e1, e2) -> 
    Pathd (lift n e, lift n e1, lift n e2)
  | e -> e

(* Unfolds all declared env constants and checks for naming conflicts *)

let rec unfold_all env vars = function
  | Global x -> 
    begin 
      match unfold x env with
      | Ok (body, _) -> Ok body
      | _ -> Ok (Global x)
    end

  | Lam (x, e) ->
    if is_declared x env then
      Error ("Naming conflict with the name '" ^ x ^ 
        "'\nIt occurs as definition/theorem identifier but is used as a variable name ")
    else
      begin match unfold_all env vars e with
      | Ok e' -> 
        Ok (Lam (x, e'))
      | Error msg -> Error msg
      end

  | Pabs (x, e) -> 
    if is_declared x env then
      Error ("Naming conflict with the name '" ^ x ^ 
        "'\nIt occurs as definition/theorem identifier but is used as a variable name ")
    else
      begin match unfold_all env vars e with
      | Ok e' -> 
        Ok (Pabs (x, e'))
      | Error msg -> Error msg
      end

  | App (e1, e2) ->
    let u1 = unfold_all env vars e1 in
    let u2 = unfold_all env vars e2 in
    begin match u1, u2 with
      | Ok e1', Ok e2' -> Ok (App (e1', e2'))
      | Error msg, _ | _, Error msg -> Error msg
    end

  | At (e1, e2) ->
    let u1 = unfold_all env vars e1 in
    let u2 = unfold_all env vars e2 in
    begin match u1, u2 with
      | Ok e1', Ok e2' -> Ok (At (e1', e2'))
      | Error msg, _ | _, Error msg -> Error msg
    end

  | Abort e -> 
    begin match unfold_all env vars e with
    | Ok e' -> 
      Ok (Abort e')
    | Error msg -> Error msg
    end

  | Pi (x, e1, e2) -> 
    if is_declared x env then
      Error ("Naming conflict with the name '" ^ x ^ "'\nIt occurs as definition/theorem identifier but is used as a variable name ")
    else
      let u1 = unfold_all env vars e1 in
      let u2 = unfold_all env vars e2 in
      begin match u1, u2 with
      | Ok e1', Ok e2' -> Ok (Pi (x, e1', e2'))
      | Error msg, _ | _, Error msg -> Error msg
      end

  | Pathd (e, e1, e2) -> 
    let u = unfold_all env vars e in
    let u1 = unfold_all env vars e1 in
    let u2 = unfold_all env vars e2 in
    begin match u, u1, u2 with
      | Ok e', Ok e1', Ok e2' -> Ok (Pathd (e', e1', e2'))
      | Error msg, _, _ | _, Error msg , _ | _, _, Error msg -> Error msg
    end
  
  | Coe (i, j, e1, e2) ->
    let ui = unfold_all env vars i in
    let uj = unfold_all env vars j in
    let u1 = unfold_all env vars e1 in
    let u2 = unfold_all env vars e2 in
    begin match ui, uj, u1, u2 with
      | Ok i', Ok j', Ok e1', Ok e2' -> Ok (Coe (i', j', e1', e2'))
      | Error msg, _, _, _ | _, Error msg , _, _ | _, _, Error msg, _ | _, _, _, Error msg -> 
        Error msg
    end
  
  | Hcom (i, j, e, e1, e2) ->
    let ui = unfold_all env vars i in
    let uj = unfold_all env vars j in
    let u = unfold_all env vars e in
    let u1 = unfold_all env vars e1 in
    let u2 = unfold_all env vars e2 in
    begin match ui, uj, u, u1, u2 with
      | Ok i', Ok j', Ok e', Ok e1', Ok e2' -> Ok (Hcom (i', j', e', e1', e2'))
      | Error msg, _, _, _, _ | _, Error msg , _, _, _ | _, _, Error msg, _, _ | _, _, _, Error msg, _ | _, _, _, _, Error msg -> Error msg
    end 

  | e -> Ok e 