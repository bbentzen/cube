(**
 * (c) Copyright 2026 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Internal core syntax using de Bruijn indices for local variables.
 *       Binder names are preserved as formatting hints for the pretty printer.
 **)

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
  | Hfill of expr * expr * expr
  | Abs of string * expr
  | App of expr * expr
  | Pi of string * expr * expr
  | Pair of expr * expr
  | Fst of expr
  | Snd of expr
  | Sigma of string * expr * expr
  | Zero of unit
  | Succ of expr
  | Natrec of expr * expr * expr
  | Nat of unit
  | Abort of expr
  | Void of unit
  | Pabs of string * expr
  | At of expr * expr
  | Pathd of expr * expr * expr
  | Type of level
  | Hole of string * (expr list)
  | Wild of int
  | Subgoal of unit

type proof =
  | Prf of string * (((string list * expr) * bool) list) * expr * expr

let rec lt = function
  | Num 0, _ -> true
  | Num n, Num m -> n <= m
  | Var n, Var m -> n = m
  | Max (n, n'), Max (m, m') -> 
    lt (Max (n, n'), m) || lt (Max (n, n'), m')
  | Max (n, n'), m ->
    lt (n, m) && lt (n', m)
  | n, Max (m, m') ->
    lt (n, m) || lt (n, m')
  | Suc n, Suc m -> lt (n, m)
  | Num n, Suc m -> lt (Num (n-1), m)
  | n, Suc m -> lt (n, m)
  | Var par, _  | _, Var par  when par.[0] = '?' -> true (* Level placeholders *)
  | Suc _, _ | Num _, Var _ | Var _, Num _ -> false

let leq (m, n) = m = n || lt (m, n)

let rec unieval = function
  | Suc n -> Suc (unieval n)
  | Max (Suc n, m) | Max (m, Suc n) -> 
    Suc (unieval (Max (n, m)))
  | Max (n, m) ->
    if leq(n, m) then
      unieval m
    else if leq(m, n) then
      unieval n
    else
      Max (unieval n, unieval m)
  | l -> l

let rec parametrize_level = function
  | Num l -> Num l 
  | Var s -> Var ("?" ^ s)
  | Suc l -> Suc (parametrize_level l)
  | Max (l1, l2) -> Max (parametrize_level l1, parametrize_level l2)

let rec parametrize_levels = function
  | Type lvl -> Type (parametrize_level lvl)
  | Pi (x, l1, l2) -> Pi (x, parametrize_levels l1, parametrize_levels l2)
  | Sigma (x, l1, l2) -> Sigma (x, parametrize_levels l1, parametrize_levels l2)
  | Coe (i, j, l1, l2) -> Coe (parametrize_levels i, parametrize_levels j, parametrize_levels l1, parametrize_levels l2)
  | Hfill (l1, l2, l3) -> Hfill (parametrize_levels l1, parametrize_levels l2, parametrize_levels l3)
  | App (l1, l2) -> App (parametrize_levels l1, parametrize_levels l2)
  | Pair (l1, l2) -> Pair (parametrize_levels l1, parametrize_levels l2)
  | Fst l -> Fst (parametrize_levels l)
  | Snd l -> Snd (parametrize_levels l)
  | Succ l -> Succ (parametrize_levels l)
  | Natrec (l1, l2, l3) -> Natrec (parametrize_levels l1, parametrize_levels l2, parametrize_levels l3)
  | Abort l -> Abort (parametrize_levels l)
  | Pabs (s, l) -> Pabs (s, parametrize_levels l)
  | At (l1, l2) -> At (parametrize_levels l1, parametrize_levels l2)
  | Pathd (l1, l2, l3) -> Pathd (parametrize_levels l1, parametrize_levels l2, parametrize_levels l3)
  | Hole (s, ls) -> Hole (s, List.map parametrize_levels ls)
  | e -> e

(* Hash table for tracking inductive type information *)

type constr_spec = {
  c_name : string;
  c_num_args : int;
  c_rec_args : bool list; (* true for recursive arguments requiring IH *)
}

type ind_spec = {
  ind_name : string;
  num_indices : int;
  num_params : int;
  constructors : constr_spec list;
}