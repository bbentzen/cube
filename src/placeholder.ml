(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Operations involving placeholders
 **)

open Core_ast

(* Counts the number of placeholders in an expression, generates a new one *)

let rec count = function
  | Hole _ -> 1
  | Fst e | Snd e | Inl e | Inr e 
  | Succ e | Abort e| Abs (_, e) | Pabs (_, e) -> 
    count e 
  | App (e1, e2) | Pair (e1, e2) | Sum (e1, e2) 
  | Let (e1, e2) | At(e1, e2) | Pi (_, e1, e2) | Sigma (_, e1, e2) -> 
    count e1 + count e2
  | Case (e, e1, e2) | Natrec (e, e1, e2) 
  | Pathd (e, e1, e2) | Hfill (e, e1, e2) -> 
    count e + count e1 + count e2
  | Coe (i, j, e1, e2) -> 
    count i + count j + count e1 + count e2
  | _ -> 0

let generate e hole l = 
  Hole ((string_of_int ((count e) + hole)), l)

(* Returns the type of a term variable when it has been declared *)

let rec candidates = function (* TODO: remove duplicates *)
  | Hole (n, l) ->
    [n, l]
  | Abs (_, e) | Pabs (_, e) -> 
    candidates e
  | Fst e | Snd e | Inl e | Inr e | Succ e | Abort e -> 
    candidates e
  | Pi (_, e1, e2) | Sigma (_, e1, e2) -> 
    candidates e1 @ candidates e2
  | App (e1, e2) | Pair (e1, e2) | Sum (e1, e2) | Let (e1, e2) | At(e1, e2) -> 
    candidates e1 @ candidates e2
  | Case (e, e1, e2) | Natrec (e, e1, e2) | Pathd (e, e1, e2) -> 
    candidates e @ candidates e1 @ candidates e2
  | _ -> []

(* Determines whether an expression is or has a placeholder/underscore *)

let is = function
  | Hole _ | Wild _ -> true
  | _ -> false

let rec has_placeholder = function
  | Hole _ -> true
  | Abs (_, e) | Pabs (_, e) -> 
    has_placeholder e 
  | Pi (_, e1, e2) | Sigma (_, e1, e2) -> 
    has_placeholder e1 || has_placeholder e2
  | Fst e | Snd e | Inl e | Inr e | Succ e | Abort e -> 
    has_placeholder e
  | App (e1, e2) | Pair (e1, e2) | Sum (e1, e2) | Let (e1, e2) | At(e1, e2) -> 
    has_placeholder e1 || has_placeholder e2
  | Case (e, e1, e2) | Natrec (e, e1, e2) | Pathd (e, e1, e2) | Hfill (e, e1, e2) -> 
    has_placeholder e || has_placeholder e1 || has_placeholder e2
  | Coe (i, j, e1, e2) -> 
    has_placeholder i || has_placeholder j || has_placeholder e1 || has_placeholder e2
  | _ -> false

(* Determines whether an expression has underscores *)

let rec has_underscore = function
  | Wild _ -> 
    true
  | Abs (_, e) | Pabs (_, e) -> 
    has_underscore e 
  | Pi (_, e1, e2) | Sigma (_, e1, e2) -> 
    has_underscore e1 || has_underscore e2
  | Fst e | Snd e | Inl e | Inr e | Succ e | Abort e -> 
    has_underscore e
  | App (e1, e2) | Pair (e1, e2) | Sum (e1, e2) | Let (e1, e2) | At(e1, e2) -> 
    has_underscore e1 || has_underscore e2
  | Case (e, e1, e2) | Natrec (e, e1, e2) | Pathd (e, e1, e2) | Hfill (e, e1, e2) -> 
    has_underscore e || has_underscore e1 || has_underscore e2
  | Coe (i, j, e1, e2) -> 
    has_underscore i || has_underscore j || has_underscore e1 || has_underscore e2
  | _ -> false

let rec preforget n e =
  let h n = Hole (string_of_int n, []) in
  match e with
  | Global _ -> h n, n (* was Global y *)
  | Local index -> Local index, n
  | Coe (_, _, _, _) ->
    Coe (h n, h (n+1), h (n+2), h (n+3)), n+4
  | Hfill (_, _, _) -> 
    Hfill (h n, h (n+1), h (n+2)), n+3
  | Abs (y, _) -> 
    Abs (y, h n), n+1
  | App (_, _) -> 
    App (h n, h (n+1)), n+2
  | Pair (_, _) -> 
    Pair (h n, h (n+1)), n+2
  | Fst _ -> 
    Fst (h n), n+1
  | Snd _ -> 
    Snd (h n), n+1
  | Pi (y, Hole (k, l), e) ->
    let e', n' = preforget n e in
    Pi (y, Hole (k, l), e'), n'
  | Pi (y, _, _) -> 
    Pi (y, h n, h (n+1)), n+2
  | Sigma (y, _, _) -> 
    Sigma (y, h n, h (n+1)), n+2
  | Inl _ -> 
    Inl (h n), n+1
  | Inr _ -> 
    Inr (h n), n+1
  | Case (_, _, _) -> 
    Case (h n, h (n+1), h (n+2)), n+3
  | Sum (_, _) -> 
    Sum (h n, h (n+1)), n+2
  | Succ _ -> 
    Succ (h n), n+1
  | Natrec (_, _, _) -> 
    Natrec (h n, h (n+1), h (n+2)), n+3
  | Let (_, _) -> 
    Let (h n, h (n+1)), n+2
  | Abort _ -> 
    Abort (h n), n+1
  | Pabs (y, _) -> 
    Pabs (y, h n), n+1
  | At (_, _) -> 
    At (h n, h (n+1)), n+2
  | Pathd (_, _, _) -> 
    Pathd (h n, h (n+1), h (n+2)), n+3
  | Wild 0 -> 
    h n, n+1
  | e -> e, n

let forget ph e =
    fst (preforget ph e)

(* Has either placeholders or underscores *)
  
let rec has = function
  | Wild _ | Hole _ -> true
  | Abs (_, e) | Pabs (_, e) -> has e
  | Pi (_, e1, e2) | Sigma (_, e1, e2) -> has e1 || has e2
  | Fst e | Snd e | Inl e | Inr e | Succ e | Abort e -> has e
  | App (e1, e2) | Pair (e1, e2) | Sum (e1, e2) | Let (e1, e2) | At(e1, e2) -> has e1 || has e2
  | Case (e, e1, e2) | Natrec (e, e1, e2) | Pathd (e, e1, e2) | Hfill (e, e1, e2) -> has e || has e1 || has e2
  | Coe (i, j, e1, e2) -> has i || has j || has e1 || has e2
  | _ -> false