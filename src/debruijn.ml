(**
 * (c) Copyright 2026 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Translation between user raw AST and internal de Bruijn AST.
 *       Free identifiers remain globals and bound identifiers become local indices. 
 *       This also file handles operations on local variables, objects 
 *       "Local <index>" of type "expr" of core expressions, which 
 *       are identified as indices in pure de Bruijn form.
 **)

open Core_ast

let rec index_of x = function
  | [] -> None
  | y :: env -> if x = y then Some 0 else Option.map (fun n -> n + 1) (index_of x env)

let rec name_at n = function
  | [] -> "(ERROR: dangling local variable " ^ string_of_int n ^ ")" (* failwith "name_at: empty environment" *)
  | x :: _ when n = 0 -> x
  | _ :: env -> name_at (n - 1) env

let rec level_of_raw = function
  | Ast.Num n -> Core_ast.Num n
  | Ast.Var x -> Core_ast.Var x
  | Ast.Suc l -> Core_ast.Suc (level_of_raw l)
  | Ast.Max (l1, l2) -> Core_ast.Max (level_of_raw l1, level_of_raw l2)

let rec to_raw_level = function
  | Core_ast.Num n -> Ast.Num n
  | Core_ast.Var x -> Ast.Var x
  | Core_ast.Suc l -> Ast.Suc (to_raw_level l)
  | Core_ast.Max (l1, l2) -> Ast.Max (to_raw_level l1, to_raw_level l2)

let rec of_raw_expr_with_env env = function
  | Ast.Id x ->
    begin
      match index_of x env with
      | Some index -> Core_ast.Local index
      | None -> Core_ast.Global x
    end
  | Ast.Int () -> Core_ast.Int ()
  | Ast.I1 () -> Core_ast.I1 ()
  | Ast.I0 () -> Core_ast.I0 ()
  | Ast.Coe (i, j, e1, e2) ->
    Core_ast.Coe (
      of_raw_expr_with_env env i,
      of_raw_expr_with_env env j,
      of_raw_expr_with_env env e1,
      of_raw_expr_with_env env e2)
  | Ast.Hfill (e, e1, e2) ->
    Core_ast.Hfill (
      of_raw_expr_with_env env e,
      of_raw_expr_with_env env e1,
      of_raw_expr_with_env env e2)
  | Ast.Abs (x, e) -> Core_ast.Abs (x, of_raw_expr_with_env (x :: env) e)
  | Ast.App (e1, e2) -> Core_ast.App (of_raw_expr_with_env env e1, of_raw_expr_with_env env e2)
  | Ast.Pi (x, e1, e2) ->
    Core_ast.Pi (x, of_raw_expr_with_env env e1, of_raw_expr_with_env (x :: env) e2)
  | Ast.Pair (e1, e2) -> Core_ast.Pair (of_raw_expr_with_env env e1, of_raw_expr_with_env env e2)
  | Ast.Fst e -> Core_ast.Fst (of_raw_expr_with_env env e)
  | Ast.Snd e -> Core_ast.Snd (of_raw_expr_with_env env e)
  | Ast.Sigma (x, e1, e2) ->
    Core_ast.Sigma (x, of_raw_expr_with_env env e1, of_raw_expr_with_env (x :: env) e2)
  | Ast.Abort e -> Core_ast.Abort (of_raw_expr_with_env env e)
  | Ast.Void () -> Core_ast.Void ()
  | Ast.Pabs (x, e) -> Core_ast.Pabs (x, of_raw_expr_with_env (x :: env) e)
  | Ast.At (e1, e2) -> Core_ast.At (of_raw_expr_with_env env e1, of_raw_expr_with_env env e2)
  | Ast.Pathd (e, e1, e2) ->
    Core_ast.Pathd (of_raw_expr_with_env env e, of_raw_expr_with_env env e1, of_raw_expr_with_env env e2)
  | Ast.Type l -> Core_ast.Type (level_of_raw l)
  | Ast.Hole (n, l) -> Core_ast.Hole (n, List.map (of_raw_expr_with_env env) l)
  | Ast.Wild n -> Core_ast.Wild n
  | Ast.Subgoal() -> Core_ast.Subgoal()

let of_raw_expr e = of_raw_expr_with_env [] e

let rec to_raw_expr_with_env env = function
  | Core_ast.Local index -> Ast.Id (name_at index env)
  | Core_ast.Global x -> Ast.Id x
  | Core_ast.Int () -> Ast.Int ()
  | Core_ast.I1 () -> Ast.I1 ()
  | Core_ast.I0 () -> Ast.I0 ()
  | Core_ast.Coe (i, j, e1, e2) ->
    Ast.Coe (
      to_raw_expr_with_env env i,
      to_raw_expr_with_env env j,
      to_raw_expr_with_env env e1,
      to_raw_expr_with_env env e2)
  | Core_ast.Hfill (e, e1, e2) ->
    Ast.Hfill (
      to_raw_expr_with_env env e,
      to_raw_expr_with_env env e1,
      to_raw_expr_with_env env e2)
  | Core_ast.Abs (x, e) -> Ast.Abs (x, to_raw_expr_with_env (x :: env) e)
  | Core_ast.App (e1, e2) -> Ast.App (to_raw_expr_with_env env e1, to_raw_expr_with_env env e2)
  | Core_ast.Pi (x, e1, e2) ->
    Ast.Pi (x, to_raw_expr_with_env env e1, to_raw_expr_with_env (x :: env) e2)
  | Core_ast.Pair (e1, e2) -> Ast.Pair (to_raw_expr_with_env env e1, to_raw_expr_with_env env e2)
  | Core_ast.Fst e -> Ast.Fst (to_raw_expr_with_env env e)
  | Core_ast.Snd e -> Ast.Snd (to_raw_expr_with_env env e)
  | Core_ast.Sigma (x, e1, e2) ->
    Ast.Sigma (x, to_raw_expr_with_env env e1, to_raw_expr_with_env (x :: env) e2)
  | Core_ast.Abort e -> Ast.Abort (to_raw_expr_with_env env e)
  | Core_ast.Void () -> Ast.Void ()
  | Core_ast.Pabs (x, e) -> Ast.Pabs (x, to_raw_expr_with_env (x :: env) e)
  | Core_ast.At (e1, e2) -> Ast.At (to_raw_expr_with_env env e1, to_raw_expr_with_env env e2)
  | Core_ast.Pathd (e, e1, e2) ->
    Ast.Pathd (to_raw_expr_with_env env e, to_raw_expr_with_env env e1, to_raw_expr_with_env env e2)
  | Core_ast.Type l -> Ast.Type (to_raw_level l)
  | Core_ast.Hole (n, l) -> Ast.Hole (n, List.map (to_raw_expr_with_env env) l)
  | Core_ast.Wild n -> Ast.Wild n
  | Core_ast.Subgoal() -> Ast.Subgoal()

let to_raw_expr e = to_raw_expr_with_env [] e

let normalize_expr e =  to_raw_expr (of_raw_expr e)

let to_raw_ctx ctx =
  let rec helper acc = function
    | [] -> List.rev acc
    | (x, ty, b) :: ctx' ->
      let ty' = to_raw_expr ty in
      helper ((x, ty', b) :: acc) ctx'
  in
  helper [] ctx

let normalize_ctx ctx =
  let rec helper env acc = function
    | [] -> List.rev acc
    | (x, ty, b) :: rest ->
      let ty' =
        ty
        |> of_raw_expr_with_env env
        |> to_raw_expr_with_env env
      in
      helper (x :: env) ((x, ty', b) :: acc) rest
  in
  helper [] [] ctx

let normalize_decl ((ids, ty), b) =
  ((ids, normalize_expr ty), b)

let normalize_proof = function
  | Ast.Prf (id, l, ty, e) ->
    Ast.Prf (id, List.map normalize_decl l, normalize_expr ty, normalize_expr e)


let rec shift cutoff amount = function
  | Local index ->
    if index >= cutoff then Local (index + amount)
    else Local index
  | Global _ | Int _ | I1 _ | I0 _ | Void _ | Type _ | Wild _ | Subgoal _ as e -> e
  | Coe (i, j, e1, e2) ->
    Coe (shift cutoff amount i, shift cutoff amount j, shift cutoff amount e1, shift cutoff amount e2)
  | Hfill (e, e1, e2) ->
    Hfill (shift cutoff amount e, shift cutoff amount e1, shift cutoff amount e2)
  | Abs (x, e) -> Abs (x, shift (cutoff + 1) amount e)
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
  | Hfill (e, e1, e2) ->
    Hfill (open_var k replacement e, open_var k replacement e1, open_var k replacement e2)
  | Abs (x, e) -> Abs (x, open_var (k + 1) replacement e)
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
  | Hfill (e, e1, e2) -> Hfill (close_var k x e, close_var k x e1, close_var k x e2)
  | Abs (y, e) -> Abs (y, close_var (k + 1) x e)
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

(* Legacy substitution function *)

let rec fullsubst k ex d b = function
  | e when e = (shift 0 k ex) -> shift 0 k d
  | Global _ | Local _ | Int _ | I1 _ | I0 _ | Void _ | Type _ | Wild _ | Subgoal _ as e -> e
  | Coe (i, j, e1, e2) -> Coe (fullsubst k ex d b i, fullsubst k ex d b j, fullsubst k ex d b e1, fullsubst k ex d b e2)
  | Hfill (e, e1, e2) -> Hfill (fullsubst k ex d b e, fullsubst k ex d b e1, fullsubst k ex d b e2)
  | Abs (y, e) -> Abs (y, fullsubst (k+1) ex d b e)
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
  | Hfill (e, e1, e2) -> occurs_index target cutoff e || occurs_index target cutoff e1 || occurs_index target cutoff e2
  | Abs (_, e) | Pabs (_, e) -> occurs_index target (cutoff + 1) e
  | App (e1, e2) | Pair (e1, e2) | At (e1, e2) -> occurs_index target cutoff e1 || occurs_index target cutoff e2
  | Pi (_, e1, e2) | Sigma (_, e1, e2) -> occurs_index target cutoff e1 || occurs_index target (cutoff + 1) e2
  | Fst e | Snd e | Abort e -> occurs_index target cutoff e
  | Pathd (e, e1, e2) ->
    occurs_index target cutoff e || occurs_index target cutoff e1 || occurs_index target cutoff e2

let rec occurs_name s hint = function
  | Abs (x, e) | Pabs (x, e) -> x = hint || occurs_name x hint e
  | Pi (x, e1, e2) | Sigma (x, e1, e2) -> x = hint || occurs_name x hint e1 || occurs_name x hint e2
  | Local _ -> s = hint | Global t -> t = hint
  | Int _ | I1 _ | I0 _ | Void _ | Type _ | Wild _ | Subgoal _ -> false
  | Hole (_, l) -> List.exists (occurs_name s hint) l
  | Coe (i, j, e1, e2) -> occurs_name s hint i || occurs_name s hint j || occurs_name s hint e1 || occurs_name s hint e2
  | Hfill (e, e1, e2) -> occurs_name s hint e || occurs_name s hint e1 || occurs_name s hint e2
  | App (e1, e2) | Pair (e1, e2) | At (e1, e2) -> occurs_name s hint e1 || occurs_name s hint e2
  | Fst e | Snd e | Abort e -> occurs_name s hint e
  | Pathd (e, e1, e2) ->
    occurs_name s hint e || occurs_name s hint e1 || occurs_name s hint e2

(* Converts a list of expressions into a single expression by application *)

let rec list_to_expr l =
  match l with
  | [] -> Core_ast.Void() (* This is arbitrary *)
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