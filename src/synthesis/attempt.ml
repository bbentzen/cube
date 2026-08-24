(**
  (c) Copyright 2019 Bruno Bentzen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  
  Desc: Basic operations on synthesization attempts, tuples
            (int * string * expr) list 
         which indicate the number of the implicit argument, 
         the constant it was filled with, and its type
 **)

open Basis

(* Print synthesization attempts *)

let rec printfst = function
  | [] -> "" 
  | (n, id, ty) :: synl' -> 
    string_of_int n ^ ", " ^ id ^ " : " ^ Pretty.printf ty ^ "\n" ^ printfst synl'

(* A synthesization attempt ?a : A is trustworthy if A is not a placeholder *)

let rec trustworthy = function
  | [] -> true
  | (_, _, ty) :: synl ->
    if Placeholder.is ty then
      false
    else
      trustworthy synl

(* Print synthesization attempts *)