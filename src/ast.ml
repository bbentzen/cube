(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: The abstract syntax of terms and types
 **)

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