(**
  (c) Copyright 2019 Bruno Bentzen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Desc: This module is the heart of the program. It executes the commands 
        described in the user's file like inductive definitions, universe 
        level declarations, proofs of theorems, term evaluation, etc. 
        Successfully compiled data are stored in a global environment.
 **)

open Basis
open Ast
open Data
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
  | Thm (cmd, Prf (id, l, ty_raw, e_raw)) ->
    let location = next_location () in
    begin
      (* Convert expressions storing the index of available fresh variable *)
      let ty, v = of_raw_expr_with_vars [] ty_raw in
      let e, v' = of_raw_expr_with_vars [] e_raw in
      let fresh_vars = fresh_var_list (v @ v') + 1 in
      (* Unfold all used global environtment identifiers *)
      match Env.unfold_all global 0 (Implicit.convert ty) with
      | Ok hty ->
        let ctx = Global.create_ctx l in
        let (h1, h2) = 
          Ctx.check global ind_env ind ctx lvl,
          let ind_ctx = Inductive.add ind ctx in
          Type.check global ind_env ind_ctx lvl (eval ind_env hty)
        in
        begin 
          match h1, h2 with
          | Ok ctx, Ok (ty', _) -> 
            let ctx' = List.rev ctx in
            begin 
              match Env.unfold_all global 0 (Implicit.convert e) with
              | Ok e' ->
                if Env.is_declared id global || Env.is_declared id ind then 
                  failwith_at location
                    ("Naming conflict with the identifier '" ^ id ^
                     "'\nName already exists in the environment (try 'infer " ^ id ^ "' for more information)")
                else
                  begin
                    (* Evaluate expressions and temporarily add inductive types to the context for type checking *)
                    let ictx = Inductive.add ind ctx' in
                    let e' = eval ind_env e' and ty' = eval ind_env ty' in
                    let res = Synthesize.init global ind_env ictx lvl e' ty' fresh_vars in
                    match res with 
                    | Ok (e1, ty1) ->
                      if id = "infer" then
                        Ok (global, ind_env, ind, ("infer := " ^ Pretty.printf e1 ^ ": \n" ^ "         " ^ Pretty.printf ty1 ^ "\n", lopen))
                      else
                        compile (Env.add global id ctx' (e1, ty1)) ind_env ind lopen filename lvl next_location cmd
                    | Error msg -> 
                      failwith_at location ("The following error was found at '" ^ id ^ "'\n" ^ msg)
                  end
              | Error msg -> 
                failwith_at location msg
            end
          | Error msg, _ -> 
            failwith_at location ("Error found at '" ^ id ^ "' when validating its context. \n" ^ msg)
          | _, Error msg  -> 
            failwith_at location ("Error found at '" ^ id ^ "' when checking typehood for the target type. \n" ^ msg)
        end
      | Error msg -> 
        failwith_at location msg
    end

  | Print (cmd, id) -> 
    let location = next_location () in
    begin 
      match Env.check_def_id id global with
      | Ok (e, ty) ->
        begin 
          match compile global ind_env ind lopen filename lvl next_location cmd with
          | Ok (global', ind_env', ind', (s, lopen)) -> 
            Ok (global', ind_env', ind', (id ^ " := \n  " ^ Pretty.printf e ^ ": \n  " ^ 
            Pretty.printf (eval ind_env ty) ^ "\n" ^ s, lopen))
          | Error msg ->
            failwith_at location msg
        end
      | Error msg -> 
        failwith_at location msg
    end
  
  | Eval (_, e_raw) -> 
    let location = next_location () in
    begin
      let e = of_raw_expr e_raw in
      match (Env.unfold_all global 0 e) with
      | Ok e' ->
        Ok (global, ind_env, ind, ("eval " ^ Pretty.printf e ^ " := " ^ 
        Pretty.printf (eval ind_env e'), lopen))
      | Error msg -> 
        failwith_at location msg
    end
  
  | Import (cmd, s) ->
    let location = next_location () in
    let path' = File.resolve_path filename s in
    if List.mem path' lopen then
      compile global ind_env ind lopen filename lvl next_location cmd
    else
      begin
        match checkfile global ind_env ind lopen path' lvl with
        | Ok (global', ind_env', ind', (_, lopen')) ->
          compile global' ind_env' ind' (path' :: lopen') filename lvl next_location cmd
        | Error msg ->
          failwith_at location msg
      end
  
  | Level (cmd, lvl') ->
    let _ = next_location () in
    compile global ind_env ind lopen filename (lvl @ lvl') next_location cmd

  | Ind (cmd, id, l, ty_raw, constrs_raw) ->
    let location = next_location () in
    begin
      (* Checks naming conflicts for the inductive type name *)
      if Env.is_declared id ind || Env.is_declared id global then
        failwith_at location
          ("Naming conflict with the inductive type identifier '" ^ id ^
           "'\nName already exists in the environment.")
      else
        let ty = of_raw_expr ty_raw in
        let ctx = Global.create_ctx l in
        let (h1, h2) =
          Ctx.check_with_universe global ind_env ctx lvl,
          Type.check global ind_env ctx lvl (eval ind_env ty)
        in
        begin match h1, h2 with
        | Ok (ctx_checked, ctx_univ), Ok (ty', _) ->
            let ctx' = List.rev ctx_checked in
            let ty_fam = Inductive.generate_type_family id ctx' ty' in

            (* Validates all constructors and stores the universes their types live in *)
            let cons_checked ind' =
              List.map (fun (c_name, c_ty_raw) ->
                if Env.is_declared c_name ind' || Env.is_declared c_name global then
                  failwith_at location
                    ("Naming conflict with constructor '" ^ c_name ^ "'")
                else
                  let c_ty = of_raw_expr c_ty_raw in
                  (* Unfolds any definitions of identifiers occuring in constructor type*)
                  begin match Env.unfold_all global 0 c_ty with
                  | Ok c_ty ->
                    let c_ty = Eval.eval ind_env c_ty in
                    (* Checks that the inductive type occurs strictly positively in the constructor type *)
                    if not (Inductive.strictly_positive ind_env id c_ty) then
                      failwith_at location
                        ("Strict positivity check failed for constructor '" ^ c_name ^
                        "' in inductive type '" ^ id ^ "'")
                    else
                      let ind_ctx = Inductive.add ((id, ty_fam) :: ind) ctx' in
                      begin match Type.check global ind_env ind_ctx lvl (eval ind_env c_ty) with
                      | Ok (c_ty', c_univ) ->
                        let c_indexed_ty = Inductive.parametrize_constructor_ty c_ty' ctx in
                        (* Store indexed, non-indexed versions, and their type universes *)
                        (c_name, c_indexed_ty), (c_name, c_ty), (c_name, c_univ)
                      | Error msg ->
                        failwith_at location
                          ("Type check failed for constructor '" ^ c_name ^
                          "' in inductive type '" ^ id ^ "':\n" ^ msg)
                      end
                  | Error msg -> failwith_at location msg
                  end
              ) constrs_raw
            in

            (* Generalize universe levels as placeholder levels *)
            let pctx = Ctx.placeholder_levels ctx' in
            let pty_fam = Inductive.generate_type_family id pctx (Level.placeholder_levels ty') in

            (* Add inductive type to the type environment *)
            let ind_ty = (id, pty_fam) :: ind in

            (* Add each constructor to the type environment *)
            let idx_constr = List.map (fun ((id, c_ty), _, _) -> (id, Level.placeholder_levels c_ty)) (cons_checked ind_ty) in
            let ind_cons =
              List.fold_left (fun l (c_name, c_ty) ->
                (c_name, c_ty) :: l) ind_ty idx_constr (* needs to turn into a list of exprs*)
            in

            (* Generate and register the eliminator (id ^ "rec") *)
            let rec_name = Inductive.rec_name id in
            if Env.is_declared rec_name ind_cons || Env.is_declared rec_name global then
              failwith_at location
                ("Naming conflict: generated eliminator '" ^ rec_name ^ "' already exists.")
            else
              let nonidx_constr = List.map (fun (_, y, _) -> y) (cons_checked ind_ty) in
              let rec_ty = Inductive.generate_recursor id ty' nonidx_constr ctx_checked pctx in (* use ctx_checked to print the ctx in order *)
              let ind_all =
                (rec_name, rec_ty) :: ind_cons
              in

              (* Validate the predicativity of the purported inductive type  *)
              let univ_constr = List.map (fun (_, _, z) -> z) (cons_checked ind_ty) in
              begin match Inductive.extract_universe_level ty' with
              | Some target_lvl ->
                if Inductive.check_universe_levels ctx_univ univ_constr (Suc target_lvl) then
                  (* Unfolds recursor and constructor environments *)
                  let rec_env, cons_env = ind_env in
                  (* Registers the inductive type data into them *)
                  let num_indices = List.length ctx_checked in
                  let num_params = Inductive.ar_type_fam ty' in
                  (* Register constructors data for recursor and type inference *)
                  let constructors = List.map (fun (c_name, c_ty') ->
                    let rec extract_args rec_acc num_args = function
                      | Pi (_, arg_ty, cod) ->
                          let is_rec = Inductive.occurs_name id [] arg_ty in
                          extract_args (is_rec :: rec_acc) (num_args + 1) cod
                      | _ -> (num_args, List.rev rec_acc)
                    in
                    let c_num_args, c_rec_args = extract_args [] 0 c_ty' in
                    (* Register data for constructor type inference *)
                    Hashtbl.add cons_env (c_name) {
                    ind_name = id;
                    num_params = num_params;
                    num_indices = num_indices};
                    (* Register constructor data for recursor generation *)
                    { c_name = c_name; 
                    c_num_args = c_num_args; 
                    c_rec_args = c_rec_args }
                  ) nonidx_constr in (* skips type indices *)
                  
                  (* Register recursor data *)
                  Hashtbl.add rec_env (id ^ "rec") {
                    ind_name = id;
                    num_params = num_params;
                    num_indices = num_indices;
                    constructors = constructors
                  };

                  (* If predicative load output and continue compiling subsequent commands *)
                  begin match compile global ind_env ind_all lopen filename lvl next_location cmd with
                  | Ok (global', ind_env', ind', (s, lopen_res)) ->
                      let log_str =
                        "inductive " ^ id ^ " successfully introduced.\n" ^ s
                      in
                      Ok (global', ind_env', ind', (log_str, lopen_res))
                  | Error msg -> failwith_at location msg
                  end
                else
                  failwith_at location
                  ("Universe level error: levels at indices or constructors of '" ^ id ^ "' may exceed target universe level " ^ 
                  Pretty.print_level target_lvl ^ ":\n" ^ Global.printf ctx_univ ^ Inductive.print univ_constr ^ "\n")
              | None ->
                failwith_at location
                ("Universe level error: Could not extract universe level from type of inductive '" ^ id ^ "'.")
              end
        | Error msg, _ | _, Error msg ->
            failwith_at location 
            ("Error in inductive declaration '" ^ id ^ "':\n" ^ msg)
      end
    end

  | Eof() -> 
    Ok (global, ind_env, ind, ("", lopen))

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
