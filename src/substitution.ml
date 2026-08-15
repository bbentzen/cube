(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Implements substituition of variables and full terms
 **)

(* Return the least fresh variable of the form v0,..,vn not occuring in two given expressions *)

let rec has_var x = function
  | Ast.Id y -> 
    if x = y then true else false
  | Ast.Abs (y, e) | Ast.Pabs (y, e) -> 
    if x = y then false else has_var x e (* if x = y then true *)
  | Ast.Pi (y, e1, e2) | Ast.Sigma (y, e1, e2) -> (* if x = y then true *)
    if x = y then false else has_var x e1 || has_var x e2
  | Ast.Fst e | Ast.Snd e | Ast.Inl e | Ast.Inr e | Ast.Succ e | Ast.Abort e -> 
    has_var x e
  | Ast.App (e1, e2) | Ast.Pair (e1, e2) | Ast.Sum (e1, e2) | Ast.At(e1, e2) -> 
    has_var x e1 || has_var x e2
  | Ast.Case (e, e1, e2) | Ast.Natrec (e, e1, e2) | Ast.Pathd (e, e1, e2) | Ast.Hfill (e, e1, e2) -> 
    has_var x e || has_var x e1 || has_var x e2
  | Ast.Coe (i, j, e1, e2) -> 
    has_var x i || has_var x j || has_var x e1 || has_var x e2
  | Ast.Type _ -> false
  | Ast.Hole (_, l) ->
    let rec helper = function
    | [] -> false
    | e :: l' ->
      has_var x e || helper l' in
      helper l
  | _ -> false

let fresh_var_int e = 
  let rec helper i e =
    if has_var ("v" ^ string_of_int (i+1)) e then 
      helper (i+1) e 
    else i 
  in  (* not free_var *)
  helper 0 e

let fresh_var e1 e2 i = 
  "v" ^ string_of_int (fresh_var_int (Ast.App (e1, e2)) + i)
