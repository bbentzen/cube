(**
  (c) Copyright 2026 Bruno Bentzen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Desc: This file contains basic operations on expressions, including shifting, opening, closing, and substituting variables. 
        Local variables are objects of the form "Local <index>" of type expr, which 
        are identified as indices in pure de Bruijn form.
**)

open Ast


let rec shift cutoff amount = function
  | Local index ->
    if index >= cutoff then Local (index + amount)
    else Local index
  | Global _ | Int _ | I1 _ | I0 _ | Void _ | Type _ | Wild _ | Subgoal _ as e -> e
  | Coe (i, j, e1, e2) ->
    Coe (shift cutoff amount i, shift cutoff amount j, shift cutoff amount e1, shift cutoff amount e2)
  | Hcom (i, j, e, e1, e2) ->
    Hcom (shift cutoff amount i, shift cutoff amount j, shift cutoff amount e, shift cutoff amount e1, shift cutoff amount e2)
  | Lam (x, e) -> Lam (x, shift (cutoff + 1) amount e)
  | App (e1, e2) -> App (shift cutoff amount e1, shift cutoff amount e2)
  | Pi (x, e1, e2) -> Pi (x, shift cutoff amount e1, shift (cutoff + 1) amount e2)
  | Pair (e1, e2) -> Pair (shift cutoff amount e1, shift cutoff amount e2)
  | Fst e -> Fst (shift cutoff amount e)
  | Snd e -> Snd (shift cutoff amount e)
  | Sigma (x, e1, e2) -> Sigma (x, shift cutoff amount e1, shift (cutoff + 1) amount e2)
  | Abort e -> Abort (shift cutoff amount e)
  | Pabs (x, e) -> Pabs (x, shift (cutoff + 1) amount e)
  | At (e1, e2) -> At (shift cutoff amount e1, shift cutoff amount e2)
  | Pathd (e, e1, e2) ->
    Pathd (shift cutoff amount e, shift cutoff amount e1, shift cutoff amount e2)
  | Hole (n, l) -> Hole (n, List.map (shift cutoff amount) l)

  (* Additional functions *)

let rec open_var k replacement = function
  | Local index ->
    if index = k then shift 0 k replacement
    else if index > k then Local (index - 1)
    else Local index
  | Global _ | Int _ | I1 _ | I0 _ | Void _ | Type _ | Wild _ | Subgoal _ as e -> e
  | Coe (i, j, e1, e2) ->
    Coe (open_var k replacement i, open_var k replacement j, open_var k replacement e1, open_var k replacement e2)
  | Hcom (i, j, e, e1, e2) ->
    Hcom (open_var k replacement i, open_var k replacement j, open_var k replacement e, open_var k replacement e1, open_var k replacement e2)
  | Lam (x, e) -> Lam (x, open_var (k + 1) replacement e)
  | App (e1, e2) -> App (open_var k replacement e1, open_var k replacement e2)
  | Pi (x, e1, e2) -> Pi (x, open_var k replacement e1, open_var (k + 1) replacement e2)
  | Pair (e1, e2) -> Pair (open_var k replacement e1, open_var k replacement e2)
  | Fst e -> Fst (open_var k replacement e)
  | Snd e -> Snd (open_var k replacement e)
  | Sigma (x, e1, e2) -> Sigma (x, open_var k replacement e1, open_var (k + 1) replacement e2)
  | Abort e -> Abort (open_var k replacement e)
  | Pabs (x, e) -> Pabs (x, open_var (k + 1) replacement e)
  | At (e1, e2) -> At (open_var k replacement e1, open_var k replacement e2)
  | Pathd (e, e1, e2) ->
    Pathd (open_var k replacement e, open_var k replacement e1, open_var k replacement e2)
  | Hole (n, l) -> Hole (n, List.map (open_var k replacement) l)

let rec close_var k x = function
  | Global y when x = y -> Local k
  | Global _ as e -> e | Local _ as e -> e | Int _ as e -> e 
  | I1 _ as e -> e | I0 _ as e -> e
  | Coe (i, j, e1, e2) -> Coe (close_var k x i, close_var k x j, close_var k x e1, close_var k x e2)
  | Hcom (i, j, e, e1, e2) -> Hcom (close_var k x i, close_var k x j, close_var k x e, close_var k x e1, close_var k x e2)
  | Lam (y, e) -> Lam (y, close_var (k + 1) x e)
  | App (e1, e2) -> App (close_var k x e1, close_var k x e2)
  | Pi (y, e1, e2) -> Pi (y, close_var k x e1, close_var (k + 1) x e2)
  | Pair (e1, e2) -> Pair (close_var k x e1, close_var k x e2)
  | Fst e -> Fst (close_var k x e)
  | Snd e -> Snd (close_var k x e)
  | Sigma (y, e1, e2) -> Sigma (y, close_var k x e1, close_var (k + 1) x e2)
  | Abort e -> Abort (close_var k x e)
  | Void _ as e -> e
  | Pabs (y, e) -> Pabs (y, close_var (k + 1) x e)
  | At (e1, e2) -> At (close_var k x e1, close_var k x e2)
  | Pathd (e, e1, e2) -> Pathd (close_var k x e, close_var k x e1, close_var k x e2)
  | Type _ as e -> e
  | Hole (n, l) -> Hole (n, List.map (close_var k x) l)
  | Wild _ as e -> e
  | Subgoal _ as e -> e

(* Abbreviations for opening and closing binders *)

let open_bound replacement body =
  open_var 0 replacement body

let close_bound binder body =
  close_var 0 binder body

(* Legacy substitution function *)

let rec fullsubst k ex d b = function
  | e when e = (shift 0 k ex) -> shift 0 k d
  | Global _ | Local _ | Int _ | I1 _ | I0 _ | Void _ | Type _ | Wild _ | Subgoal _ as e -> e
  | Coe (i, j, e1, e2) -> Coe (fullsubst k ex d b i, fullsubst k ex d b j, fullsubst k ex d b e1, fullsubst k ex d b e2)
  | Hcom (i, j, e, e1, e2) -> Hcom (fullsubst k ex d b i, fullsubst k ex d b j, fullsubst k ex d b e, fullsubst k ex d b e1, fullsubst k ex d b e2)
  | Lam (y, e) -> Lam (y, fullsubst (k+1) ex d b e)
  | App (e1, e2) -> App (fullsubst k ex d b e1, fullsubst k ex d b e2)
  | Pi (y, e1, e2) -> Pi (y, fullsubst k ex d b e1, fullsubst (k+1) ex d b e2)
  | Pair (e1, e2) -> Pair (fullsubst k ex d b e1, fullsubst k ex d b e2)
  | Fst e -> Fst (fullsubst k ex d b e)
  | Snd e -> Snd (fullsubst k ex d b e)
  | Sigma (y, e1, e2) -> Sigma (y, fullsubst k ex d b e1, fullsubst (k+1) ex d b e2)
  | Abort e -> Abort (fullsubst k ex d b e)
  | Pabs (y, e) -> Pabs (y, fullsubst (k+1) ex d b e)
  | At (e1, e2) -> At (fullsubst k ex d b e1, fullsubst k ex d b e2)
  | Pathd (e, e1, e2) -> Pathd (fullsubst k ex d b e, fullsubst k ex d b e1, fullsubst k ex d b e2)
  | Hole (n, l) -> if b then Hole (n, List.map (fun e -> fullsubst k ex d b e) l) else Hole (n, l)

(* Occurrence of indices *)

let rec occurs_index target cutoff = function
  | Local index -> index = target + cutoff
  | Global _ | Int _ | I1 _ | I0 _ | Void _ | Type _ | Wild _ | Subgoal _ -> false
  | Hole (_, l) -> List.exists (occurs_index target cutoff) l
  | Coe (i, j, e1, e2) -> occurs_index target cutoff i || occurs_index target cutoff j || occurs_index target cutoff e1 || occurs_index target cutoff e2
  | Hcom (i, j, e, e1, e2) -> occurs_index target cutoff i || occurs_index target cutoff j || occurs_index target cutoff e || occurs_index target cutoff e1 || occurs_index target cutoff e2
  | Lam (_, e) | Pabs (_, e) -> occurs_index target (cutoff + 1) e
  | App (e1, e2) | Pair (e1, e2) | At (e1, e2) -> occurs_index target cutoff e1 || occurs_index target cutoff e2
  | Pi (_, e1, e2) | Sigma (_, e1, e2) -> occurs_index target cutoff e1 || occurs_index target (cutoff + 1) e2
  | Fst e | Snd e | Abort e -> occurs_index target cutoff e
  | Pathd (e, e1, e2) ->
    occurs_index target cutoff e || occurs_index target cutoff e1 || occurs_index target cutoff e2

let rec occurs_name s hint = function
  | Lam (x, e) | Pabs (x, e) -> x = hint || occurs_name x hint e
  | Pi (x, e1, e2) | Sigma (x, e1, e2) -> x = hint || occurs_name x hint e1 || occurs_name x hint e2
  | Local _ -> s = hint | Global t -> t = hint
  | Int _ | I1 _ | I0 _ | Void _ | Type _ | Wild _ | Subgoal _ -> false
  | Hole (_, l) -> List.exists (occurs_name s hint) l
  | Coe (i, j, e1, e2) -> occurs_name s hint i || occurs_name s hint j || occurs_name s hint e1 || occurs_name s hint e2
  | Hcom (i, j, e, e1, e2) -> occurs_name s hint i || occurs_name s hint j || occurs_name s hint e || occurs_name s hint e1 || occurs_name s hint e2
  | App (e1, e2) | Pair (e1, e2) | At (e1, e2) -> occurs_name s hint e1 || occurs_name s hint e2
  | Fst e | Snd e | Abort e -> occurs_name s hint e
  | Pathd (e, e1, e2) ->
    occurs_name s hint e || occurs_name s hint e1 || occurs_name s hint e2

(* Converts a list of expressions into a single expression by application *)

let rec list_to_expr l =
  match l with
  | [] -> Void() (* This is arbitrary *)
  | e :: es -> App (e, list_to_expr es)

(* Creates n-many fresh variables from a list es of expressions *)

let create_fresh_char c es n =
  let rec helper i e n =
    if occurs_name (c ^ "0") (c ^ string_of_int i) e then
      helper (i+1) e n
    else if n > 0 then
      Array.append [| c ^ string_of_int i |] (helper (i+1) e (n-1))
    else
      [| |]
  in  (* not free_var *)
  helper 0 (list_to_expr es) n

let create_fresh es n = create_fresh_char "v" es n

let init_fresh n = "v" ^ string_of_int n