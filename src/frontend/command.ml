(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Executes the commands described in a file
 *       Sucessfully type-checked terms are stored in a global context
 **)

open Basis
open Checker
open Synthesis
open Eval
open File
open Context

let normalize_expr = Debruijn.normalize_expr

let normalize_ctx = Debruijn.normalize_ctx

let format_location location =
  Printf.sprintf "Line %d, characters %d-%d:\n"
    location.line location.col_start location.col_end

let failwith_at location msg =
  match location with
  | Some loc -> failwith (format_location loc ^ msg)
  | None -> failwith msg

let rec compile global lopen filename lvl next_location = function
  | Ast.Thm (cmd, Prf (id, l, ty, e)) ->
    let location = next_location () in
    begin
      let ty_raw = normalize_expr (Implicit.convert ty) in
      let e_raw = normalize_expr (Implicit.convert e) in
      match Global.unfold_all global 0 ty_raw with
      | Ok hty ->
        let ctx = normalize_ctx (Local.create_ctx l) in
        let (h1, h2) = 
          Ctx.check global ctx lvl, 
          Type.check global ctx lvl (reduce hty)
        in
        begin 
          match h1, h2 with
          | Ok ctx, Ok (ty', _) -> 
            let ctx' = List.rev ctx in
            begin 
              match Global.unfold_all global 0 e_raw with
              | Ok e' ->
                if Global.is_declared id global then 
                  failwith_at location
                    ("Naming conflict with the identifier '" ^ id ^
                     "'\nName already exists in the environment (try 'print " ^ id ^ "' for more information)")
                else
                  begin
                    let res = Synthesize.init global ctx' lvl (eval e') ty' in
                    match res with 
                    | Ok (e1, ty1) ->
                      let e1' = normalize_expr e1 in
                      let ty1' = normalize_expr ty1 in
                      compile (Global.add_to_global_env global id ctx' (e1', ty1')) lopen filename lvl next_location cmd
                    | Error msg -> 
                      failwith_at location ("The following error was found at '" ^ id ^ "'\n" ^ msg)
                  end
              | Error msg -> 
                failwith_at location msg
            end
          | Error msg, _ | _, Error msg -> 
            failwith_at location ("The following error was found at '" ^ id ^ "'\n" ^ msg)
        end
      | Error msg -> 
        failwith_at location msg
    end

  (* TODO: print function that evaluates expressions *)

  | Ast.Print (cmd, id) -> 
    let location = next_location () in
    begin 
      match Global.check_def_id id global with
      | Ok (e, ty) ->
        begin 
          match compile global lopen filename lvl next_location cmd with
          | Ok (global', (s, lopen)) -> 
            Ok (global', (id ^ " := \n  " ^ Pretty.print e ^ ": \n  " ^ 
            Pretty.print (Eval.eval ty) ^ "\n" ^ s, lopen))
          | Error msg ->
            failwith_at location msg
        end
      | Error msg -> 
        failwith_at location msg
    end

  | Ast.Infer (cmd, e) ->
    let location = next_location () in
    let e' = normalize_expr e in
    let h1 = Placeholder.generate e' 0 [] in
    let elab = Elab.elaborate global [] lvl ([], []) h1 0 0 e' in 
    begin 
      match elab with
      | Ok (e1, ty, _) ->
        let e'' = normalize_expr e1 in
        let ty' = normalize_expr ty in
        begin 
          match compile global lopen filename lvl next_location cmd with
          | Ok (global', (s, lopen)) -> 
            Ok (global', ("infer := " ^ Pretty.print e'' ^ ": \n" ^
              "         " ^ Pretty.print ty' ^ 
              "\n" ^ s, lopen))
          | Error msg -> failwith_at location msg
        end
      | Error (_, msg) -> 
        failwith_at location msg
    end
  
  | Ast.Eval (_, e) ->
    let location = next_location () in
    begin
      match (Global.unfold_all global 0 e) with
      | Ok e' ->
        Ok (global, ("eval " ^ Pretty.print e ^ " := " ^ 
        Pretty.print (Eval.eval e'), lopen))
      | Error msg -> 
        failwith_at location msg
    end
  
  | Ast.Import (cmd, s) ->
    let location = next_location () in
    let path' = File.resolve_path filename s in
    if List.mem path' lopen then
      compile global lopen filename lvl next_location cmd
    else
      begin
        match checkfile global lopen path' lvl with
        | Ok (global', (_, lopen')) ->
          compile global' (path' :: lopen') filename lvl next_location cmd
        | Error msg ->
          failwith_at location msg
      end
  
  | Ast.Level (cmd, lvl') ->
    let _ = next_location () in
    compile global lopen filename (lvl @ lvl') next_location cmd

  | Ast.Eof() -> 
    Ok (global, ("", lopen))
  
  

and checkfile global lopen filename lvl =
  let cmd =
    try
      parse_file filename
    with
    | Sys_error s ->
        failwith ("Failed to open the file '" ^ filename ^ "'\n" ^ s)
    | Parsing.Parse_error ->
        failwith ("Failed to parse the file '" ^ filename ^ "'")
    | Failure msg ->
        failwith ("Failed to parse the file '" ^ filename ^ "'\n" ^ msg)
  in
  let locations = ref (command_locations_of_file filename) in
  let next_location () =
    match !locations with
    | location :: rest ->
        locations := rest;
        Some location
    | [] ->
        None
  in
  compile global lopen filename lvl next_location cmd
