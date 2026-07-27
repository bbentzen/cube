(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Handles synthesization of implicit arguments and universe levels,
         Performs an exhaustive search on compatible types based on the context
         The elaborator returns a pair (sl') of its current synthesization attempts and stack
 **)

open Basis
open Checker

(* Iterated synthesization attempts *)

let rec check global ctx lvl sl e ty max =
  let e' = Debruijn.normalize_expr (Eval.eval e) in
  let ty' = Debruijn.normalize_expr (Eval.eval ty) in
  let elab = Elab.elaborate global ctx lvl sl ty' 0 0 e' in
  begin
    match elab with
    | Ok (e', ty', sl') ->

      if Attempt.trustworthy (fst sl') then
        Ok (e', ty')
      else

        let e'' = Debruijn.normalize_expr e' in
        let ty'' = Debruijn.normalize_expr ty' in
        let relab = Elab.elaborate global ctx lvl sl ty'' 0 0 e'' in
        begin
          match relab with
          | Ok _ -> 
            Ok (e', ty')
          | Error (_, msg) -> 
            iter sl' msg global ctx lvl e ty (max+1)
        end
      
    | Error (sl', msg) ->
      iter sl' msg global ctx lvl e ty (max+1)
  end

and iter sl' msg global ctx lvl e ty max =
  if max > 100 then
    Error "Maximum number of synthetization steps reached
      \n(You should not see this message, please report)"
  else

    match (fst sl') with
    | [] ->
      Error msg
    
    | (n, id, _) :: _ ->

      begin match Stack.find_index n (snd sl') with 
      | Ok _ -> 

        let e' = Substitution.prefull (Wild n) (Id id) e in
        let w = check global ctx lvl ([], snd sl') e' ty max in
        begin 
          match w with
          | Ok (e', ty') ->
            Ok (e', ty')
          | Error _ ->
            check global ctx lvl ([], Stack.mkfalse n id (snd sl')) e ty max
        end
          
      | Error _ ->
        Error ("Can't find stack for the placeholder '?" ^ id ^ 
        "'\n(You should not see this message, please report)\n")
      end

let init global ctx lvl e ty =
  check global ctx lvl ([], []) e ty 0
  