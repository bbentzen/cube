(**
  (c) Copyright 2019 Bruno Bentzen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Desc: This file governs the abstract syntax of parsed expressions and commands with named variables,
        as well as core expressions with de Bruijn indices for local variables, where binder names are 
        preserved as formatting hints for the pretty printer. It also processes raw into core expressions,
        where free identifiers remain globals and bound identifiers become local indices.
 **)

(* Raw syntax and operations used only at the parsing stage *)

type rawlevel = 
  | RNum of int
  | RVar of string
  | RSuc of rawlevel
  | RMax of rawlevel * rawlevel

type rawexpr = 
  | RId of string
  | RInt of unit
  | RI1 of unit
  | RI0 of unit
  | RCoe of rawexpr * rawexpr * rawexpr * rawexpr
  | RHcom of rawexpr * rawexpr * rawexpr * rawexpr * rawexpr 
  | RLam of string * rawexpr
  | RApp of rawexpr * rawexpr
  | RPi of string * rawexpr * rawexpr  
  | RPair of rawexpr * rawexpr
  | RFst of rawexpr
  | RSnd of rawexpr
  | RSigma of string * rawexpr * rawexpr
  | RAbort of rawexpr
  | RVoid of unit
  | RPabs of string * rawexpr
  | RAt of rawexpr * rawexpr
  | RPathd of rawexpr * rawexpr * rawexpr
  | RType of rawlevel
  | RHole of string * (rawexpr list)
  | RWild of int
  | RSubgoal of unit

let rec has_var x = function
  | RId y -> x = y
  | RLam (y, e) | RPabs (y, e) -> 
    if x = y then false else has_var x e 
  | RPi (y, e1, e2) | RSigma (y, e1, e2) -> 
    if x = y then false else has_var x e1 || has_var x e2
  | RFst e | RSnd e | RAbort e -> has_var x e
  | RApp (e1, e2) | RPair (e1, e2) | RAt(e1, e2) -> 
    has_var x e1 || has_var x e2
  | RPathd (e, e1, e2) -> 
    has_var x e || has_var x e1 || has_var x e2
  | RCoe (i, j, e1, e2) -> 
    has_var x i || has_var x j || has_var x e1 || has_var x e2
  | RHcom (i, j, e, e1, e2) -> 
    has_var x i || has_var x j || has_var x e || has_var x e1 || has_var x e2
  | RType _ -> false
  | RHole (_, l) ->
    let rec helper = function
    | [] -> false
    | e :: l' -> has_var x e || helper l' in
      helper l
  | _ -> false

let fresh_var_int e = 
  let rec helper i e =
    if has_var ("v" ^ string_of_int (i+1)) e then helper (i+1) e else i 
  in  (* not free_var *)
  helper 0 e

let fresh_var e1 e2 i =
  "v" ^ string_of_int (fresh_var_int (RApp (e1, e2)) + i)

(* The abstract syntax of commands takes raw expressions which are then converted to core expressions *)

type proof = 
  | Prf of string * (((string list * rawexpr) * bool) list) * rawexpr * rawexpr

type command = 
    | Import of command * string
    | Thm of command * proof
    | Ind of command * string * (((string list * rawexpr) * bool) list) * rawexpr * ((string * rawexpr) list)
    | Print of command * string
    | Eval of command * rawexpr
    | Level of command * string list
    | Eof of unit

(* Internal core syntax in locally nameless representation style *)

type level =
  | Num of int
  | Var of string
  | Suc of level
  | Max of level * level

type expr =
  | Local of int
  | Global of string
  | Int of unit
  | I1 of unit
  | I0 of unit
  | Coe of expr * expr * expr * expr
  | Hcom of expr * expr * expr * expr * expr
  | Lam of string * expr
  | App of expr * expr
  | Pi of string * expr * expr
  | Pair of expr * expr
  | Fst of expr
  | Snd of expr
  | Sigma of string * expr * expr
  | Abort of expr
  | Void of unit
  | Pabs of string * expr
  | At of expr * expr
  | Pathd of expr * expr * expr
  | Type of level
  | Hole of string * (expr list)
  | Wild of int
  | Subgoal of unit

(* Conversion of raw expressions into expressions *)

let rec index_of x = function
  | [] -> None
  | y :: env -> if x = y then Some 0 else Option.map (fun n -> n + 1) (index_of x env)

let rec name_at n = function
  | [] -> "(ERROR: dangling local variable " ^ string_of_int n ^ ")"
  | x :: _ when n = 0 -> x
  | _ :: env -> name_at (n - 1) env

let rec level_of_raw = function
  | RNum n -> Num n
  | RVar x -> Var x
  | RSuc l -> Suc (level_of_raw l)
  | RMax (l1, l2) -> Max (level_of_raw l1, level_of_raw l2)

let rec to_raw_level = function
  | Num n -> RNum n
  | Var x -> RVar x
  | Suc l -> RSuc (to_raw_level l)
  | Max (l1, l2) -> RMax (to_raw_level l1, to_raw_level l2)

let rec of_raw_expr_with_env env = function
  | RId x ->
    begin
      match index_of x env with
      | Some index -> Local index
      | None -> Global x
    end
  | RInt () -> Int ()
  | RI1 () -> I1 ()
  | RI0 () -> I0 ()
  | RCoe (i, j, e1, e2) ->
    Coe (
      of_raw_expr_with_env env i,
      of_raw_expr_with_env env j,
      of_raw_expr_with_env env e1,
      of_raw_expr_with_env env e2)
  | RHcom (i, j, e, e1, e2) ->
    Hcom (
      of_raw_expr_with_env env i,
      of_raw_expr_with_env env j,
      of_raw_expr_with_env env e,
      of_raw_expr_with_env env e1,
      of_raw_expr_with_env env e2)
  | RLam (x, e) -> Lam (x, of_raw_expr_with_env (x :: env) e)
  | RApp (e1, e2) -> App (of_raw_expr_with_env env e1, of_raw_expr_with_env env e2)
  | RPi (x, e1, e2) ->
    Pi (x, of_raw_expr_with_env env e1, of_raw_expr_with_env (x :: env) e2)
  | RPair (e1, e2) -> Pair (of_raw_expr_with_env env e1, of_raw_expr_with_env env e2)
  | RFst e -> Fst (of_raw_expr_with_env env e)
  | RSnd e -> Snd (of_raw_expr_with_env env e)
  | RSigma (x, e1, e2) ->
    Sigma (x, of_raw_expr_with_env env e1, of_raw_expr_with_env (x :: env) e2)
  | RAbort e -> Abort (of_raw_expr_with_env env e)
  | RVoid () -> Void ()
  | RPabs (x, e) -> Pabs (x, of_raw_expr_with_env (x :: env) e)
  | RAt (e1, e2) -> At (of_raw_expr_with_env env e1, of_raw_expr_with_env env e2)
  | RPathd (e, e1, e2) ->
    Pathd (of_raw_expr_with_env env e, of_raw_expr_with_env env e1, of_raw_expr_with_env env e2)
  | RType l -> Type (level_of_raw l)
  | RHole (n, l) -> Hole (n, List.map (of_raw_expr_with_env env) l)
  | RWild n -> Wild n
  | RSubgoal() -> Subgoal()

(* Returns a core expression with a list of used variable identifiers *)

let rec of_raw_expr_with_vars env = function
  | RId x ->
    (* Stores integers n for every identifier of the form "v" ^ n *)
    let e = 
      begin match index_of x env with
      | Some index -> Local index
      | None -> Global x
      end 
    and n = 
      if x.[0] = 'v' then
        let s = Base.String.drop_prefix x 1 in
        begin match int_of_string_opt s with
            | Some n -> [n]
            | None -> []
        end
      else 
        []
    in
    e, n
  | RInt () -> Int (), []
  | RI1 () -> I1 (), []
  | RI0 () -> I0 (), []
  | RCoe (i, j, e1, e2) ->
    let i', vi = of_raw_expr_with_vars env i in
    let j', vj = of_raw_expr_with_vars env j in
    let e1', v1 = of_raw_expr_with_vars env e1 in
    let e2', v2 = of_raw_expr_with_vars env e2 in
    Coe (i', j', e1', e2'), vi @ vj @ v1 @ v2
  | RHcom (i, j, e, e1, e2) ->
    let i', vi = of_raw_expr_with_vars env i in
    let j', vj = of_raw_expr_with_vars env j in
    let e', ve = of_raw_expr_with_vars env e in
    let e1', v1 = of_raw_expr_with_vars env e1 in
    let e2', v2 = of_raw_expr_with_vars env e2 in
    Hcom (i', j', e', e1', e2'), vi @ vj @ ve @ v1 @ v2
  | RLam (x, e) ->
    let e', v = of_raw_expr_with_vars (x :: env) e in
    Lam (x, e'), v
  | RApp (e1, e2) ->
    let e1', v1 = of_raw_expr_with_vars env e1 in
    let e2', v2 = of_raw_expr_with_vars env e2 in
    App (e1', e2'), v1 @ v2
  | RPi (x, e1, e2) ->
    let e1', v1 = of_raw_expr_with_vars env e1 in
    let e2', v2 = of_raw_expr_with_vars (x :: env) e2 in
    Pi (x, e1', e2'), v1 @ v2
  | RPair (e1, e2) ->
    let e1', v1 = of_raw_expr_with_vars env e1 in
    let e2', v2 = of_raw_expr_with_vars env e2 in
    Pair (e1', e2'), v1 @ v2
  | RFst e ->
    let e', v = of_raw_expr_with_vars env e in
    Fst e', v
  | RSnd e ->
    let e', v = of_raw_expr_with_vars env e in
    Snd e', v
  | RSigma (x, e1, e2) ->
    let e1', v1 = of_raw_expr_with_vars env e1 in
    let e2', v2 = of_raw_expr_with_vars (x :: env) e2 in
    Sigma (x, e1', e2'), v1 @ v2
  | RAbort e ->
    let e', v = of_raw_expr_with_vars env e in
    Abort e', v
  | RVoid () -> Void (), []
  | RPabs (x, e) ->
    let e', v = of_raw_expr_with_vars (x :: env) e in
    Pabs (x, e'), v
  | RAt (e1, e2) ->
    let e1', v1 = of_raw_expr_with_vars env e1 in
    let e2', v2 = of_raw_expr_with_vars env e2 in
    At (e1', e2'), v1 @ v2
  | RPathd (e, e1, e2) ->
    let e', v = of_raw_expr_with_vars env e in
    let e1', v1 = of_raw_expr_with_vars env e1 in
    let e2', v2 = of_raw_expr_with_vars env e2 in
    Pathd (e', e1', e2'), v @ v1 @ v2
  | RType l -> Type (level_of_raw l), []
  | RHole (n, l) -> 
    let of_raw_expr_with_vars_fst = fun x -> fst (of_raw_expr_with_vars env x) in
    Hole (n, List.map of_raw_expr_with_vars_fst l), []
  | RWild n -> Wild n, []
  | RSubgoal() -> Subgoal(), []

let fresh_var_list l =
  List.fold_left (fun acc n -> n + acc) 0 l

let of_raw_expr e = fst (of_raw_expr_with_vars [] e)
