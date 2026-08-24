(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Basic operations on synthesization stacks, lists of lists
            ((int * (string * expr * bool) list) list)
         used to keep track of which synthetization attempts have been performed
 **)

open Basis

(* Print synthesization list *)

let printb synl =
  let rec printrev = function
    | [] -> "" 
    | (id, ty, b) :: synl' -> 
      " " ^ id ^ " : " ^ Pretty.printf ty ^ "- " ^ string_of_bool b ^ "\n" ^ printrev synl'
  in
  printrev (List.rev synl)

let rec printsl = function
  | [] -> "" 
  | (n, synl) :: l -> 
    "wildcard " ^ string_of_int n ^ ":\n" ^ printb synl ^ printsl l

(* Search *) 

let rec find_index n = function
  | [] -> Error "Can't find match"
  | (m, sctx) :: l ->
    if m = n then
      Ok sctx
    else
      find_index n l

let uniq ctx =
  let helper = Hashtbl.create (List.length ctx) in
  List.iter (fun x -> Hashtbl.replace helper x ()) ctx;
  Hashtbl.fold (fun x () xs -> x :: xs) helper []

let newfind_index n tbl =
  if Hashtbl.mem tbl n then Ok (Hashtbl.find tbl n)
  else Error "Can't find match"

let lappend sa sa1 sa2 = (fst sa @ fst sa1 @ fst sa2, snd sa @ snd sa1 @ snd sa2)

let append sa1 sa2 = (fst sa1 @ fst sa2, snd sa1 @ snd sa2)