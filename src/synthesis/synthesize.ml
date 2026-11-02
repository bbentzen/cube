(**
  (c) Copyright 2019 Bruno Bentzen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  
  Desc: Handles synthesization of implicit arguments and universe levels,
         Performs an exhaustive search on compatible types based on the context
         The elaborator returns a pair (sl') of its current synthesization attempts and stack
 **)

open Basis
open Eval
open Checker

(* Stores realizers if there are no wildcards left in the synthesization attempts *)

let store_proof e ty sl =
  Hashtbl.clear Data.meta_store;
  if Attempt.trustworthy (fst sl) then
    Ok (e, ty)
  else
    Error ("Untrustworthy synthesization attempt with " 
    ^ Attempt.printfst (fst sl) ^ 
    "\nYou should not see this message, please report.")

(* Iterated synthesization attempts *)

let rec check global ctx lvl sl e ty max vars =
  let num_of_attempts = 0 in (* We're currently not rechecking elaborated terms, so they should not be trusted until kernel typechecked (= reelaborated) *)
  let allow_escaped = true in (* We're also temporarily allowing metas to escape, but in the future this should be flagged as false *)
  let e = eval e and ty = eval ty in
  let elab = Elab.elaborate global ctx lvl sl ty vars [] e in
  begin
    match elab with
    | Ok (e1, ty1, _) ->
      (* Type check the elaborated terms until no escaping metavariables remain *)
    let rec typecheck e1 ty1 sl = function
    | 0 ->
      if not (Expr.escaping_metas e1 ty1) || allow_escaped then
        store_proof e1 ty1 sl
      else
        if Expr.occurs_meta e1 then Placeholder.escaping "term" e1
        else Placeholder.escaping "type" ty1
    | n ->
      (* Zonk all metas and revert explicit substitutions *)
      let e' = Placeholder.solve [] e1 and ty' = Placeholder.solve [] ty1 in
      match Elab.elaborate global ctx lvl ([], []) ty vars [] e' with
      | Ok (e', ty', sl) ->
        if not (Expr.escaping_metas e' ty') || allow_escaped then
          store_proof e' ty' sl
        else 
          typecheck e' ty' sl (n-1)
      | Error (_, msg) -> 
        (* Useful msg for testing: *)
        (* Error ("First elaboration pass: \n" ^ Pretty.printf e1 ^ "\n" ^ Pretty.printf ty1 ^ "\n\n" ^ "After zonking, fully elaborated term\n  " ^ Pretty.printf e' ^ "\n fully elaborated type after zonking\n  " ^ Pretty.printf ty' ^ 
        Msg.meta_solutions () ^ 
        "\nTypechecking failed for the following reasons: " ^ msg) *)
        Error ( string_of_int n ^ "Kernel cannot check that the elaborated term\n  " 
        ^ Pretty.printf e' ^ "\n has the elaborated type\n  " ^ Pretty.printf ty' 
        ^ "\nTypechecking failed for the following reasons: " ^ msg)
    in
    typecheck e1 ty1 sl num_of_attempts
    | Error (sl', msg) ->
      iter sl' msg global ctx lvl e ty (max+1) vars
  end

and iter sl' msg global ctx lvl e ty max vars =
  if max > 100 then
    Error "Maximum number of synthetization steps reached
      \n(You should not see this message, please report)"
  else
    let current, past = sl' in
    match current with
    | [] -> Error msg
    | (n, id, _) :: current' ->
      let e' = Expr.fullsubst 0 (Wild n) (Global id) true e in
      let w = check global ctx lvl ([], past) e' ty max vars in
      begin 
        match w with
        | Ok (e', ty') ->
          Ok (e', ty')
        | Error _ ->
          check global ctx lvl (current', (n, id) :: past) e ty max vars
      end

let init global ctx lvl e ty vars =
  check global ctx lvl ([], []) e ty 0 vars