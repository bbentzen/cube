(**
  (c) Copyright 2019 Bruno Bentzen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Desc: The pretty printer supports special unicode characters, indents homogeneous compositions, 
        distinguishes between dependent and non-dependent functions, products, and paths,
        prints nested lambdas, pis, sigmas, and uses parentheses when necessary.
 **)

open Ast
open Expr

(* A simple pretty printer *)

let rec print env = function
  | Global("zero") -> "0 "
  | Global("nat") -> "ℕ "
  | Global y -> y ^ " "
  | Local index -> (name_at index env) ^ " "
  | Coe (i, j, e1, e2) -> String.concat "" ["coe "; parenthesize env i; parenthesize env j; parenthesize env e1; parenthesize env e2]
  
  | Hcom (i, j, e, e1, e2) -> 
    String.concat "" ["\n  hcom "; parenthesize env i; parenthesize env j; parenthesize env e; 
    "\n    | i0 → "; print env e1; 
    "\n    | i1 → "; print env e2]
    
  | Lam (x, e) ->  
    let rec iterate env = function
      | Lam (x', e') -> " " ^ x' ^ iterate (x' :: env)  e'
      | e' -> ", " ^ print env e'
    in
    "λ " ^ x ^ iterate (x :: env) e

  | Pabs (y, e) -> String.concat "" ["<"; y; "> "; print (y :: env) e]

  | Pi (x, e1, e2) ->
    if occurs_index 0 0 e2 then
      let rec iterate env = function
        | Pi (x', e1', e2') ->
          if occurs_index 0 0 e2' then
            String.concat "" ["("; x'; " : "; print env e1'; ") "; iterate (x' :: env) e2']
          else
            String.concat "" [tparenthesize env e1'; "→ "; print (x' :: env) e2']
        | e' -> print env e'
      in
      "Π (" ^ x ^ " : " ^ print (x :: env) e1 ^ ") " ^ iterate (x :: env) e2
    else
      begin match e2 with
        | Void() -> "¬" ^ tparenthesize (x :: env) e1
        | _ ->
          let rec iterate env = function
            | Pi (_, e1', Void()) -> "¬" ^ tparenthesize env e1'
            | Pi (x', e1', e2') ->
              if occurs_index 0 0 e2' then
                String.concat "" ["Π ("; x'; " : "; print env e1'; ") "; print (x' :: env) e2']
              else
                String.concat "" [tparenthesize env e1'; "→ "; iterate (x' :: env) e2']
            | e' -> print env e'
          in
          tparenthesize (x :: env) e1 ^ "→ " ^ iterate (x :: env) e2
      end

  | Sigma (x, e1, e2) ->
    if occurs_index 0 0 e2 then
      begin
      let rec iterate env = function
        | Sigma (x', e1', e2') ->
          if occurs_index 0 0 e2' then
            String.concat "" ["("; x'; " : "; print env e1'; ") "; iterate (x' :: env) e2']
          else
            String.concat "" [tparenthesize env e1'; "× "; print (x' :: env) e2']
        | e' -> print env e'
      in
      "Σ (" ^ x ^ " : " ^ print (x :: env) e1 ^ ") " ^ iterate (x :: env) e2
      end
    else
      let rec iterate env = function
        | Sigma (x', e1', e2') ->
          if occurs_index 0 0 e2' then
            String.concat "" ["Σ ("; x'; " : "; print env e1'; ") "; print (x' :: env) e2']
          else
            String.concat "" [tparenthesize env e1'; "× "; iterate (x' :: env) e2']
        | e' ->
          print env e'
      in
      tparenthesize env e1 ^ "× " ^ iterate (x :: env) e2

  | Pathd (e, e1, e2) ->
    begin
      match e with
      | Lam (i, ty) ->
        if not (occurs_index 0 0 ty) then
          "path " ^ parenthesize env ty ^ parenthesize env e1 ^ parenthesize env e2
        else
          "pathd (" ^ print env (Lam (i, ty)) ^ ") " ^ parenthesize env e1 ^ parenthesize env e2
      | _ ->
        "pathd " ^ parenthesize env e ^ parenthesize env e1 ^ parenthesize env e2
    end

  | App (e1, e2) ->
      let rec iterate = function
      | App (e3, e4) -> iterate e3 ^ parenthesize env e4
      | e -> parenthesize env e
    in
    iterate e1 ^ parenthesize env e2

  | Type l -> 
    "type " ^ print_level l ^ " "

  | Pair (e1, e2) -> "(" ^ parenthesize env e1 ^ ", " ^ parenthesize env e2 ^ ") "
  | Fst e -> "fst " ^ parenthesize env e
  | Snd e -> "snd " ^ parenthesize env e
  | Abort e -> String.concat "" ["abort "; parenthesize env e]
  | At (e1, e2) -> String.concat "" [parenthesize env e1; "@ "; parenthesize env e2]
  | Hole (n, _) -> "?" ^ n ^ "? "
  | I0() -> "i0 "
  | I1() -> "i1 "
  | Int() -> "I " 
  | Void() -> "void "
  | Wild n -> "?0" ^ string_of_int n ^ "? "
  | Subgoal() -> "?"

and parenthesize env e = 
  let helper = function
    | Lam _ | Pabs _ | Pi _ | Sigma _ | Fst _ | Snd _ 
    | Abort _ | App _ | Pair _ 
    | At _ | Pathd _ | Coe _ -> true
    | _ -> false
  in
  if helper e then
    "(" ^ print env e ^ ") "
  else
    print env e


and tparenthesize env e = 
  let helper = function
    | Pi _ | Sigma _ | Pathd _ | Hcom _ | Coe _ -> true
    | _ -> false
  in
  if helper e then
    "(" ^ print env e ^ ") "
  else
    print env e

and print_level = function
  | Num n -> string_of_int n
  | Suc n -> print_level n ^ "+ 1"
  | Var l -> l
  | Max (n, Num m) | Max (Num m, n) -> "max(" ^ print_level n ^ ", " ^ string_of_int m ^ ")"
  | Max (n, m) -> "max(" ^ print_level n ^ ", " ^ print_level m ^ ")"

(* Prints expressions in raw syntax form *)

let printf e = print [] e