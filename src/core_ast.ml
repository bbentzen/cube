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
  | Inl of expr
  | Inr of expr
  | Case of expr * expr * expr
  | Sum of expr * expr
  | Star of unit
  | Let of expr * expr
  | Unit of unit
  | True of unit
  | False of unit
  | If of expr * expr * expr
  | Bool of unit
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

let rec leq = function
  | Num 0, _ -> 
    true

  | Num n, Num m -> 
    n <= m

  | Var n, Var m -> 
    n = m

  | Max (n, n'), Max (m, m') -> 
    leq (Max (n, n'), m) || leq (Max (n, n'), m')

  | Max (n, n'), m ->
    leq (n, m) && leq (n', m)

  | n, Max (m, m') ->
    leq (n, m) || leq (n, m')

  | Suc n, Suc m -> 
    leq (n, m)
  
  | Num n, Suc m -> 
    leq (Num (n-1), m)

  | n, Suc m -> 
    leq (n, m)

  | Suc _, _ | Num _, Var _ | Var _, Num _ -> 
    false

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
