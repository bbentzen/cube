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
  | Hcom of expr * expr * expr * expr * expr
  | Abs of string * expr
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

type proof =
  | Prf of string * (((string list * expr) * bool) list) * expr * expr

(* Universe level evaluation and comparison by flattening on lists of atoms *)

let is_placeholderlvl = function
    | Var s -> String.length s > 0 && s.[0] = '?'
    | _ -> false

let rec leq k l =
    if k = l then true
    else
      match k, l with
      | Var x, _ when is_placeholderlvl (Var x) -> true
      | _, Var y when is_placeholderlvl (Var y) -> true

      | Num 0, _ -> true
      | Num n, Num m -> n <= m
      | Num n, Suc k -> leq (Num (n - 1)) k
      | Num n, Max(b1, b2) -> leq (Num n) b1 || leq (Num n) b2
      | Suc k, Suc l -> leq k l
      | Suc k, Num m -> if m = 0 then false else leq k (Num (m - 1))
      | Suc k, Max(b1, b2) -> leq (Suc k) b1 || leq (Suc k) b2

      | Var x, Suc k -> leq (Var x) k
      | Var x, Var y -> x = y
      | Var _, Num _ -> false
      | Var x, Max(k1, k2) -> leq (Var x) k1 || leq (Var x) k2

      | Max(k1, k2), l -> leq k1 l && leq k2 l

      | _ -> false

let rec unieval = function
  | Suc (Num n) -> Num (n + 1)
  | Max (Num n, Num m) -> Num (n + m)
  | Suc n -> Suc (unieval n)
  | Max (Suc n, m) | Max (m, Suc n) -> 
    Suc (unieval (Max (n, m)))
  | Max (n, m) ->
    if leq n m then
      unieval m
    else if leq m n then
      unieval n
    else
      Max (unieval n, unieval m)
  | l -> l

let rec placeholder_level = function
  | Num l -> Num l 
  | Var s -> Var ("?" ^ s)
  | Suc l -> Suc (placeholder_level l)
  | Max (l1, l2) -> Max (placeholder_level l1, placeholder_level l2)

let rec placeholder_levels = function
  | Type lvl -> Type (placeholder_level lvl)
  | Pi (x, l1, l2) -> Pi (x, placeholder_levels l1, placeholder_levels l2)
  | Sigma (x, l1, l2) -> Sigma (x, placeholder_levels l1, placeholder_levels l2)
  | Coe (i, j, l1, l2) -> Coe (placeholder_levels i, placeholder_levels j, placeholder_levels l1, placeholder_levels l2)
  | Hcom (i, j, l1, l2, l3) -> Hcom (placeholder_levels i, placeholder_levels j, placeholder_levels l1, placeholder_levels l2, placeholder_levels l3)
  | App (l1, l2) -> App (placeholder_levels l1, placeholder_levels l2)
  | Pair (l1, l2) -> Pair (placeholder_levels l1, placeholder_levels l2)
  | Fst l -> Fst (placeholder_levels l)
  | Snd l -> Snd (placeholder_levels l)
  | Abort l -> Abort (placeholder_levels l)
  | Pabs (s, l) -> Pabs (s, placeholder_levels l)
  | At (l1, l2) -> At (placeholder_levels l1, placeholder_levels l2)
  | Pathd (l1, l2, l3) -> Pathd (placeholder_levels l1, placeholder_levels l2, placeholder_levels l3)
  | Hole (s, ls) -> Hole (s, List.map placeholder_levels ls)
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