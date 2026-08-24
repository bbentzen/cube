(**
  (c) Copyright 2019 Bruno Bentzen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  
  Desc: Reads implicit arguments by enumerating them
 **)

open Basis
open Ast

(* Replaces 0-indexed wildcards with uniquely assigned indices starting at n *)

let rec read n = function
  | Coe (i, j, e1, e2) ->
    let r_i = read n i in
    let r_j = read (snd r_i) j in
    let r_e1 = read (snd r_j) e1 in
    let r_e2 = read (snd r_e1) e2 in
    Coe (fst r_i, fst r_j, fst r_e1, fst r_e2), snd r_e2
  | Hcom (i, j, e, e1, e2) ->
    let r_i = read n i in
    let r_j = read (snd r_i) j in
    let r_e = read (snd r_j) e in
    let r_e1 = read (snd r_e) e1 in
    let r_e2 = read (snd r_e1) e2 in
    Hcom (fst r_i, fst r_j, fst r_e, fst r_e1, fst r_e2), snd r_e2
  | Lam (y, e) ->
    let r_e = read n e in
    Lam (y, fst r_e), snd r_e
  | App (e1, e2) ->
    let r_e1 = read n e1 in
    let r_e2 = read (snd r_e1) e2 in
    App (fst r_e1, fst r_e2), snd r_e2
  | Pair (e1, e2) ->
    let r_e1 = read n e1 in
    let r_e2 = read (snd r_e1) e2 in
    Pair (fst r_e1, fst r_e2), snd r_e2
  | Fst e -> 
    let r_e = read n e in
    Fst (fst r_e), snd r_e
  | Snd e -> 
    let r_e = read n e in
    Snd (fst r_e), snd r_e
  | Pi (y, e1, e2) ->
    let r_e1 = read n e1 in
    let r_e2 = read (snd r_e1) e2 in
    Pi (y, fst r_e1, fst r_e2), snd r_e2
  | Sigma (y, e1, e2) ->
    let r_e1 = read n e1 in
    let r_e2 = read (snd r_e1) e2 in
    Sigma (y, fst r_e1, fst r_e2), snd r_e2
  | Abort e ->
    let r_e = read n e in
    Abort (fst r_e), snd r_e
  | Pabs (y, e) ->
    let r_e = read n e in
    Pabs (y, fst r_e), snd r_e
  | At (e1, e2) ->
    let r_e1 = read n e1 in
    let r_e2 = read (snd r_e1) e2 in
    At (fst r_e1, fst r_e2), snd r_e2
  | Pathd (e, e1, e2) ->
    let r_e = read n e in
    let r_e1 = read (snd r_e) e1 in
    let r_e2 = read (snd r_e1) e2 in
    Pathd (fst r_e, fst r_e1, fst r_e2), snd r_e2
  | Wild 0 -> 
    Wild n, n+1
  | Wild m -> 
    Wild m, n+m
  | e -> e, n

let convert e = fst (read 1 e)