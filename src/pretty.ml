(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: The pretty printer indents hfill terms, 
         distinguishes between dependent and non-dependent functions, products, and paths,
          prints nested lambdas, pis, sigmas, and uses parentheses when necessary
 **)

open Ast

(* A simple pretty printer *)

let rec print = function
  | Id("zero") -> "0 "
  | Id("nat") -> "ℕ "
  | Coe (i, j, e1, e2) -> 
    String.concat "" ["coe "; par i; par j; par e1; par e2]
  
  | Hfill (e, e1, e2) -> 
    String.concat "" ["\n  hfill "; par e; 
    "\n    | i0 → "; print e1; 
    "\n    | i1 → "; print e2]
    
  | Abs (y, e) ->  
    let rec iter = function
      | Abs (y', e') ->
        " " ^ y' ^ iter e'
      | e' ->
        ", " ^ print e'
    in
    "λ " ^ y ^ iter e

  | Pi (x, e1, e2) ->

    if Substitution.has_var x e2 then
      begin
      let rec diter = function
        | Pi (x', e1', e2') ->
          if Substitution.has_var x' e2' then
            String.concat "" ["("; x'; " : "; print e1'; ") "; diter e2']
          else
            String.concat "" [tpar e1'; "→ "; print e2']
        | e' ->
          print e'
      in
      "Π (" ^ x ^ " : " ^ print e1 ^ ") " ^ diter e2
      end

    else
      begin
        match e2 with
        | Void() -> 
          "¬" ^ tpar e1
        | _ ->
          let rec iter = function
            | Pi (x', e1', e2') ->
              if Substitution.has_var x' e2' then
                String.concat "" ["Π ("; x'; " : "; print e1'; ") "; print e2']
              else
                String.concat "" [tpar e1'; "→ "; iter e2']
            | e' ->
              print e'
          in
          tpar e1 ^ "→ " ^ iter e2
      end

  | Sigma (x, e1, e2) ->
    
    if Substitution.has_var x e2 then
      begin
      let rec diter = function
        | Sigma (x', e1', e2') ->
          if Substitution.has_var x' e2' then
            String.concat "" ["("; x'; " : "; print e1'; ") "; diter e2']
          else
            String.concat "" [tpar e1'; "× "; print e2']
        | e' ->
          print e'
      in
      "Σ (" ^ x ^ " : " ^ print e1 ^ ") " ^ diter e2
      end

    else
      let rec iter = function
        | Sigma (x', e1', e2') ->
          if Substitution.has_var x' e2' then
            String.concat "" ["Σ ("; x'; " : "; print e1'; ") "; print e2']
          else
            String.concat "" [tpar e1'; "× "; iter e2']
        | e' ->
          print e'
      in
      tpar e1 ^ "× " ^ iter e2

  | Pathd (e, e1, e2) ->
    begin
      match e with
      | Abs (i, ty) ->
        if not (Substitution.has_var i ty) then
          "path " ^ par ty ^ par e1 ^ par e2
        else
          "pathd (" ^ print (Abs (i, ty)) ^ ") " ^ par e1 ^ par e2
      | _ ->
        "pathd " ^ par e ^ par e1 ^ par e2
    end

  | App (e1, e2) ->
      let rec iter = function
      | App (e3, e4) -> iter e3 ^ par e4
      | e -> par e
    in
    iter e1 ^ par e2    

  | Type l -> 
    "type " ^ print_level l ^ " "

  | Pair (e1, e2) -> "(" ^ par e1 ^ ", " ^ par e2 ^ ") "
  | Fst e -> "fst " ^ par e
  | Snd e -> "snd " ^ par e
  | Abort e -> String.concat "" ["abort "; par e]
  | Pabs (y, e) -> String.concat "" ["<"; y; "> "; print e]
  | At (e1, e2) -> String.concat "" [par e1; "@ "; par e2]
  | Hole (n, _) -> "?" ^ n ^ "? "
  | Id y -> y ^ " "
  | I0() -> "i0 "
  | I1() -> "i1 "
  | Int() -> "I " 
  | Void() -> "void "
  | Wild n -> "?0" ^ string_of_int n ^ "? "
  | Subgoal() -> "?"

and par e = 
  let helper = function
    | Abs _ | Ast.Pabs _ | Pi _ | Sigma _ | Fst _ | Snd _ 
    | Abort _ | App _ | Pair _ 
    | At _ | Pathd _ | Coe _ -> true
    | _ -> false
  in
  if helper e then
    "(" ^ print e ^ ") "
  else
    print e

and tpar e = 
let helper = function
  | Pi _ | Sigma _ | Pathd _ | Hfill _ | Coe _ -> 
    true
  | _ -> false
in
if helper e then
  "(" ^ print e ^ ") "
else
  print e

and print_level = function
  | Num n -> string_of_int n
  | Suc n -> print_level n ^ "+ 1"
  | Var l -> l
  | Max (n, Num m) | Max (Num m, n) -> "max(" ^ print_level n ^ ", " ^ string_of_int m ^ ")"
  | Max (n, m) -> "max(" ^ print_level n ^ ", " ^ print_level m ^ ")"

(* Translates expressions back to raw syntax and prints them *)

let printf e = print (Debruijn.to_raw_expr e)

(* A core-syntax printer for debugging *)

let rec printc = function  
  | Core_ast.Coe (i, j, e1, e2) -> 
    String.concat "" ["coe "; parc i; parc j; parc e1; parc e2]
  
  | Hfill (e, e1, e2) -> 
    String.concat "" ["\n  hfill "; parc e; 
    "\n    | i0 → "; printc e1; 
    "\n    | i1 → "; printc e2]
    
  | Abs (y, e) ->  
    let rec iter = function
      | Core_ast.Abs (y', e') ->
        " " ^ y' ^ iter e'
      | e' ->
        ", " ^ printc e'
    in
    "λ " ^ y ^ iter e

  | Core_ast.Pi (x, e1, e2) ->

      let rec diter = function
        | Core_ast.Pi (x', e1', e2') ->
            String.concat "" ["("; x'; " : "; printc e1'; ") "; diter e2']
        | e' ->
          printc e'
      in
      "Π (" ^ x ^ " : " ^ printc e1 ^ ") " ^ diter e2

  | Core_ast.Sigma (x, e1, e2) ->
    

      let rec diter = function
        | Core_ast.Sigma (x', e1', e2') ->
            String.concat "" ["("; x'; " : "; printc e1'; ") "; diter e2']
        | e' ->
          printc e'
      in
      "Σ (" ^ x ^ " : " ^ printc e1 ^ ") " ^ diter e2


  | Pathd (e, e1, e2) ->
    begin
      match e with
      | Core_ast.Abs (i, ty) ->
          "pathd (" ^ printc (Core_ast.Abs (i, ty)) ^ ") " ^ parc e1 ^ parc e2
      | _ ->
        "pathd " ^ parc e ^ parc e1 ^ parc e2
    end

  | Core_ast.App (e1, e2) ->
      let rec iter = function
      | Core_ast.App (e3, e4) -> "(" ^ iter e3 ^ parc e4 ^ ")"
      | e -> "(" ^ parc e ^ ")"
    in
    iter e1 ^ parc e2

  | Type l -> 
    "type " ^ printc_level l ^ " "

  | Core_ast.Pair (e1, e2) -> "(" ^ parc e1 ^ ", " ^ parc e2 ^ ") "
  | Core_ast.Fst e -> "fst " ^ parc e
  | Core_ast.Snd e -> "snd " ^ parc e
  | Core_ast.Abort e -> String.concat "" ["abort "; parc e]
  | Core_ast.Pabs (y, e) -> String.concat "" ["<"; y; "> "; printc e]
  | Core_ast.At (e1, e2) -> String.concat "" [parc e1; "@ "; parc e2]
  | Hole (n, _) -> "?" ^ n ^ "? "
  | Global y -> " " ^ y ^ " "
  | Local index -> "Local" ^ string_of_int index ^ " "
  | I0() -> "i0 "
  | I1() -> "i1 "
  | Int() -> "I " 
  | Void() -> "void "
  | Wild n -> "?0" ^ string_of_int n ^ "? "
  | Subgoal() -> "?"

and parc e = 
  let helper = function
    | Core_ast.Abs _ | Pabs _ | Pi _ | Sigma _ | Fst _ | Snd _ 
    | Abort _ | App _ | Pair _ 
    | At _ | Pathd _ | Coe _ -> 
      true
    | _ -> false
  in
  if helper e then
    "(" ^ printc e ^ ") "
  else
    printc e

and tparc e = 
let helper = function
  | Core_ast.Pi _ | Sigma _ | Pathd _ | Hfill _ | Coe _ -> 
    true
  | _ -> false
in
if helper e then
  "(" ^ printc e ^ ") "
else
  printc e

and printc_level = function
  | Num n -> string_of_int n
  | Suc n -> printc_level n ^ "+ 1"
  | Var l -> l
  | Max (n, Num m) | Max (Num m, n) -> printc_level n ^ " + " ^ string_of_int m
  | Max (n, m) -> "max(" ^ printc_level n ^ ", " ^ printc_level m ^ ")"