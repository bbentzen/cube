(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: This file handles operations on the context and converts precontexts to actual contexts, 
 *       which are lists (string * expr * bool) where the strings are global variables 
 *       in the locally nameless representation style.     
 **)

open Basis
open Core_ast
open Debruijn

(* Replaces a global variable x with a given expression d *)

let rec subst_global k d x = function
  | Global y when x = y -> shift 0 k d
  | Global _ | Local _ | Int _ | I1 _ | I0 _ | Star _ | Unit _ | Zero _ | Nat _ | Void _ | Type _ | Wild _ | Subgoal _ as e -> e
  | Coe (i, j, e1, e2) -> Coe (subst_global k d x i, subst_global k d x j, subst_global k d x e1, subst_global k d x e2)
  | Hfill (e, e1, e2) -> Hfill (subst_global k d x e, subst_global k d x e1, subst_global k d x e2)
  | Abs (y, e) -> Abs (y, subst_global (k+1) d x e)
  | App (e1, e2) -> App (subst_global k d x e1, subst_global k d x e2)
  | Pi (y, e1, e2) -> Pi (y, subst_global k d x e1, subst_global (k+1) d x e2)
  | Pair (e1, e2) -> Pair (subst_global k d x e1, subst_global k d x e2)
  | Fst e -> Fst (subst_global k d x e)
  | Snd e -> Snd (subst_global k d x e)
  | Sigma (y, e1, e2) -> Sigma (y, subst_global k d x e1, subst_global (k+1) d x e2)
  | Inl e -> Inl (subst_global k d x e)
  | Inr e -> Inr (subst_global k d x e)
  | Case (e, e1, e2) -> Case (subst_global k d x e, subst_global k d x e1, subst_global k d x e2)
  | Sum (e1, e2) -> Sum (subst_global k d x e1, subst_global k d x e2)
  | Let (e1, e2) -> Let (subst_global k d x e1, subst_global k d x e2)
  | Succ e -> Succ (subst_global k d x e)
  | Natrec (e, e1, e2) -> Natrec (subst_global k d x e, subst_global k d x e1, subst_global k d x e2)
  | Abort e -> Abort (subst_global k d x e)
  | Pabs (y, e) -> Pabs (y, subst_global (k+1) d x e)
  | At (e1, e2) -> At (subst_global k d x e1, subst_global k d x e2)
  | Pathd (e, e1, e2) -> Pathd (subst_global k d x e, subst_global k d x e1, subst_global k d x e2)
  | Hole (n, l) -> Hole (n, List.map (subst_global k d x) l)

(* Creates a context (a list (string * expr * bool)) from a list (string list * raw expr * bool) *)

let rec create_ctx = function
  | [] -> []
  | ((ids, ty), b) :: l ->
    begin match ids with
      | [] -> []
      | e :: ids' ->
        let ty' = Debruijn.of_raw_expr ty in
        (e, ty', b) :: create_ctx ([((ids', ty), b)]) @ create_ctx l 
        (* this can be optimized since you don't want to translate the same type 
        over and over again when parsing identifiers of the same type*)
    end

(* Determines whether a variable has been declared *)

let is_declared x ctx =
  let rec helper x = function
    | [] -> false
    | (y, _, _) :: ctx -> 
      if x = y then
        true
      else
        helper x ctx
  in
  helper x (List.rev ctx)

let rec var_type x ctx =
  match (List.rev ctx) with
  | [] -> Error()
  | (y, ty, _) :: ctx' -> 
    if x = y then 
      Ok ty
    else 
      var_type x ctx'

(* Determines whether a given typed variable occurs in the context *)

let rec check_var_ty x ty ctx =
  match (List.rev ctx) with
  | [] -> false 
  | (y, ty', _) :: ctx -> 
    if x = y && ty' = ty then 
      true
    else
      check_var_ty x ty ctx

(* Finds a variable of a given type in the context when it exists *)

let find_ty ty ctx =
  let rec helper ty = function
    | [] -> Error () 
    | (y, ty', _) :: ctx -> 
      if ty' = ty then 
        Ok y
      else 
        helper ty ctx
  in
  helper ty (List.rev ctx)

let find_true ty ctx =
  let rec helper ty = function
    | [] -> Error () 
    | (y, ty', b) :: ctx' -> 
      if ty' = ty && b then 
        Ok y
      else 
        helper ty ctx'
  in
  helper ty (List.rev ctx)

(* Prints the context *)

let print ctx = 
  let rec printrev = function
    | [] -> "" 
    | (id, ty, _) :: ctx -> 
      " " ^ id ^ " : " ^ Pretty.print ty ^ "\n" ^ printrev ctx
  in
  printrev (List.rev ctx)

let printf ctx = print (Debruijn.to_raw_ctx ctx)