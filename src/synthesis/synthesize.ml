(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Handles synthesization of implicit arguments and universe levels,
         Performs an exhaustive search on compatible types based on the context
         The elaborator returns a pair (sl') of its current synthesization attempts and stack
 **)

open Basis
open Eval
open Checker

(* Iterated synthesization attempts *)

let rec check global ind_env ctx lvl sl e ty max =
  let e' = eval ind_env e in
  let ty' = eval ind_env ty in
  let elab = Elab.elaborate global ind_env ctx lvl sl ty' 0 0 e' in
  begin
    match elab with
    | Ok (e', ty', sl') ->

      if Attempt.trustworthy (fst sl') then
        Ok (e', ty')
      else

        let e'' = eval ind_env e' in
        let ty'' = eval ind_env ty' in
        let relab = Elab.elaborate global ind_env ctx lvl sl ty'' 0 0 e'' in
        begin
          match relab with
          | Ok _ -> 
            Ok (e', ty')
          | Error (_, msg) -> 
            iter sl' msg global ind_env ctx lvl e ty (max+1)
        end
      
    | Error (sl', msg) ->
      iter sl' msg global ind_env ctx lvl e ty (max+1)
  end

and iter sl' msg global ind_env ctx lvl e ty max =
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

        let e' = Debruijn.fullsubst 0 (Wild n) (Global id) true e in
        let w = check global ind_env ctx lvl ([], snd sl') e' ty max in
        begin 
          match w with
          | Ok (e', ty') ->
            Ok (e', ty')
          | Error _ ->
            check global ind_env ctx lvl ([], Stack.mkfalse n id (snd sl')) e ty max
        end
          
      | Error _ ->
        Error ("Can't find stack for the placeholder '?" ^ id ^ 
        "'\n(You should not see this message, please report)\n")
      end

let init global ind_env ctx lvl e ty =
  check global ind_env ctx lvl ([], []) e ty 0
  