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

let format_location location =
  Printf.sprintf "Line %d, characters %d-%d:\n"
    location.line location.col_start location.col_end

let failwith_at location msg =
  match location with
  | Some loc -> failwith (format_location loc ^ msg)
  | None -> failwith msg

  (* Ind_env is a pair with inductive families in hasthtable and context forms *)

let rec compile global ind_env ind lopen filename lvl next_location = function
  | Ast.Thm (cmd, Prf (id, l, ty_raw, e_raw)) ->
    let location = next_location () in
    begin
      let ty = Debruijn.of_raw_expr ty_raw in
      let e = Debruijn.of_raw_expr e_raw in
      match Env.unfold_all global 0 (Implicit.convert ty) with
      | Ok hty ->
        let ctx = Global.create_ctx l in
        let (h1, h2) = 
          Ctx.check global ctx lvl,
          let ind_ctx = Inductive.add ind ctx in
          Type.check global ind_ctx lvl (eval hty)
        in
        begin 
          match h1, h2 with
          | Ok ctx, Ok (ty', _) -> 
            let ctx' = List.rev ctx in
            begin 
              match Env.unfold_all global 0 (Implicit.convert e) with
              | Ok e' ->
                if Env.is_declared id global then 
                  failwith_at location
                    ("Naming conflict with the identifier '" ^ id ^
                     "'\nName already exists in the environment (try 'print " ^ id ^ "' for more information)")
                else
                  begin
                    (* Temporarily adds inductive types to the context for type checking *)
                    let ind_ctx = Inductive.add ind ctx' in
                    let res = Synthesize.init global ind_ctx lvl (eval e') ty' in
                    match res with 
                    | Ok (e1, ty1) ->
                      if id = "" then
                        Ok (global, ("infer := " ^ Pretty.printf e1 ^ ": \n" ^ "         " ^ Pretty.printf ty1 ^ "\n", lopen))
                      else
                        compile (Env.add global id ctx' (e1, ty1)) ind_env ind lopen filename lvl next_location cmd
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

  | Ast.Print (cmd, id) -> 
    let location = next_location () in
    begin 
      match Env.check_def_id id global with
      | Ok (e, ty) ->
        begin 
          match compile global ind_env ind lopen filename lvl next_location cmd with
          | Ok (global', (s, lopen)) -> 
            Ok (global', (id ^ " := \n  " ^ Pretty.printf e ^ ": \n  " ^ 
            Pretty.printf (eval ty) ^ "\n" ^ s, lopen))
          | Error msg ->
            failwith_at location msg
        end
      | Error msg -> 
        failwith_at location msg
    end
  
  | Ast.Eval (_, e_raw) -> 
    let location = next_location () in
    begin
      let e = Debruijn.of_raw_expr e_raw in
      match (Env.unfold_all global 0 e) with
      | Ok e' ->
        Ok (global, ("eval " ^ Pretty.print e_raw ^ " := " ^ 
        Pretty.printf (eval e'), lopen))
      | Error msg -> 
        failwith_at location msg
    end
  
  | Ast.Import (cmd, s) ->
    let location = next_location () in
    let path' = File.resolve_path filename s in
    if List.mem path' lopen then
      compile global ind_env ind lopen filename lvl next_location cmd
    else
      begin
        match checkfile global ind_env ind lopen path' lvl with
        | Ok (global', (_, lopen')) ->
          compile global' ind_env ind (path' :: lopen') filename lvl next_location cmd
        | Error msg ->
          failwith_at location msg
      end
  
  | Ast.Level (cmd, lvl') ->
    let _ = next_location () in
    compile global ind_env ind lopen filename (lvl @ lvl') next_location cmd

  | Ast.Ind (cmd, id, l, ty_raw, constrs_raw) ->
    let location = next_location () in
    begin
      (* Checks naming conflicts for the inductive type name *)
      if Env.is_declared id ind || Env.is_declared id global then
        failwith_at location
          ("Naming conflict with the inductive type identifier '" ^ id ^
           "'\nName already exists in the environment.")
      else
        let ty = Debruijn.of_raw_expr ty_raw in
        let ctx = Global.create_ctx l in
        let (h1, h2) =
          Ctx.check_with_universe global ctx lvl,
          Type.check global ctx lvl (eval ty)
        in
        begin match h1, h2 with
        | Ok (ctx_checked, ctx_univ), Ok (ty', _) ->
            let ctx' = List.rev ctx_checked in
            let ty_fam =  snd (snd (Env.function_of_def id ctx' (Core_ast.Global id, ty') 0)) in

            (* Validates all constructors and stores the universes their types live in *)
            let cons_checked ind' =
              List.map (fun (c_name, c_ty_raw) ->
                if Env.is_declared c_name ind' || Env.is_declared c_name global then
                  failwith_at location
                    ("Naming conflict with constructor '" ^ c_name ^ "'")
                else
                  let c_ty = Debruijn.of_raw_expr c_ty_raw in
                  if not (Inductive.strictly_positive id c_ty) then
                    failwith_at location
                      ("Strict positivity check failed for constructor '" ^ c_name ^
                       "' in inductive type '" ^ id ^ "'")
                  else
                    let ind' = Inductive.add [(id, ty_fam)] ctx' in
                    begin match Type.check global ind' lvl (eval c_ty) with
                    | Ok (c_ty', c_univ) -> 
                      (c_name, c_ty'), (c_name, c_univ)
                    | Error msg ->
                      failwith_at location
                        ("Type check failed for constructor '" ^ c_name ^
                         "' in inductive type '" ^ id ^ "':\n" ^ msg)
                    end
              ) constrs_raw
            in

            (* Add inductive type to the type environment *)
            let ind_ty = (id, ty_fam) :: ind in

            (* Add each constructor to the type environment *)
            let cons_checked' = List.map fst (cons_checked ind_ty) in
            let ind_cons =
              List.fold_left (fun l (c_name, c_ty) ->
                (c_name, c_ty) :: l) ind_ty cons_checked' (* needs to turn into a list of exprs*)
            in

            (* Generate and register the eliminator (id ^ "rec") *)
            let rec_name = Inductive.rec_name id in
            if Env.is_declared rec_name ind_cons || Env.is_declared rec_name global then
              failwith_at location
                ("Naming conflict: generated eliminator '" ^ rec_name ^ "' already exists.")
            else
              let constrs = cons_checked' in
              let rec_ty = Inductive.generate_recursor id ty' constrs ctx_checked ctx' in (* use ctx_checked to print the ctx in order *)
              let ind_all =
                (rec_name, rec_ty) :: ind_cons
              in

              (* Validate the predicativity of the purported inductive type  *)
              let c_univs = List.map snd (cons_checked ind_ty) in
              begin match Inductive.extract_universe_level ty' with
              | Some target_lvl ->
                if Inductive.check_universe_levels ctx_univ c_univs (Suc target_lvl) then
                  
                  (* Registers the inductive type into a hash table *)

                  let num_indices = List.length ctx_checked in
                  let num_params = Inductive.ar_type_fam ty' in
                  let constructors = List.map (fun (c_name, c_ty') ->
                    let rec extract_args rec_acc num_args = function
                      | Core_ast.Pi (_, arg_ty, cod) ->
                          let is_rec = Inductive.occurs_name id [] arg_ty in
                          extract_args (is_rec :: rec_acc) (num_args + 1) cod
                      | _ -> (num_args, List.rev rec_acc)
                    in
                    let c_num_args, c_rec_args = extract_args [] 0 c_ty' in
                    { Core_ast.c_name = c_name; 
                    Core_ast.c_num_args = c_num_args; 
                    Core_ast.c_rec_args = c_rec_args }
                  ) cons_checked' in
                  
                  Hashtbl.add ind_env id {
                    Core_ast.ind_name = id;
                    Core_ast.num_params = num_params;
                    Core_ast.num_indices = num_indices;
                    Core_ast.constructors = constructors
                  };

                  (* If predicative load output and continue compiling subsequent commands *)
                  begin match compile global ind_env ind_all lopen filename lvl next_location cmd with
                  | Ok (global_res, (s, lopen_res)) ->
                      let log_str =
                        "inductive " ^ id ^ " successfully checked and added with " ^
                        Inductive.print_spec id (Hashtbl.find ind_env id) ^ ".\n" ^ s
                      in
                      Ok (global_res, (log_str, lopen_res))
                  | Error msg -> failwith_at location msg
                  end
                else
                  failwith_at location
                  ("Universe level error: Parameter level at '" ^ id ^ "' exceeds target universe level.")
              | None ->
                failwith_at location
                ("Universe level error: Could not extract universe level from type of inductive '" ^ id ^ "'.")
              end
        | Error msg, _ | _, Error msg ->
            failwith_at location 
            ("Error in inductive declaration '" ^ id ^ "':\n" ^ msg)
      end
    end

  | Ast.Eof() -> 
    Ok (global, ("", lopen))

and checkfile global ind_env ind lopen filename lvl =
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
  compile global ind_env ind lopen filename lvl next_location cmd
