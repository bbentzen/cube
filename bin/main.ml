(**
  (c) Copyright 2019 Bruno Bentzen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Desc: The main program.
 **)

open Frontend
open Command
open Basis

let () =
  let start = Sys.time() in
  let filename =
  if Array.length Sys.argv > 1 then
    Sys.argv.(1)
  else (
    print_endline "Usage: cubicle <filename>";
    exit 1
  )
  in
  (* Initialize the hasthtable of inductive families and parse file *)
  let ind_env : (string, Data.ind_spec) Hashtbl.t = Hashtbl.create 16 in
  match checkfile [] ind_env [] [] filename [] with 
  | Ok (env, _, _, (s, _)) ->
    let n = String.length s in
    let s' = 
      if n > 0 && s.[n-1] = '\n' then 
        String.sub s 0 (n-1)
      else 
        s
    in
    print_endline s';
    let time = string_of_float (Sys.time() -. start) in
    print_endline (string_of_int (List.length env) ^ " theorem(s) compiled successfully in " ^ time ^ " seconds");
  | Error msg -> print_endline ("Error: " ^ msg);
