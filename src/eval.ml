(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Eager evaluation with full β-reduction on redexes of all types,
 *       η-reduction for dependent functions and paths,
 *       but not ε-reduction (i0/i1 endpoints) for dependent paths.
 **)

open Debruijn
open Core_ast

(* Beta reduction without index shifting *)

let beta body arg =
  Debruijn.open_var 0 arg body

(* Break an application tree into head and argument list *)

let rec break_args acc = function
  | Core_ast.App (f, arg) -> break_args (arg :: acc) f
  | head -> (head, acc)

(* Rebuild application tree from head and argument list *)

let build_app head args =
  List.fold_left (fun acc arg -> Core_ast.App (acc, arg)) head args

(* Return the position of the constructor with the given name *)

let rec find_constructor_position c_name = function
  | [] -> None
  | c_spec :: rest ->
      if c_spec.c_name = c_name then
        Some 0
      else
        match find_constructor_position c_name rest with
        | Some index -> Some (index + 1)
        | None -> None

(* Reduces a well-applied recursor of an inductive family *)

let reduce_recursor rec_spec args =
  let num_minors = List.length rec_spec.constructors in
  let expected_args = rec_spec.num_params + 1 + num_minors + rec_spec.num_indices + 1 in

  if List.length args < expected_args then
    None (* Not fully applied yet *)
  else
    let indices, rest1 = Base.List.split_n args rec_spec.num_indices in
    let motive, rest2 = (List.hd rest1, List.tl rest1) in
    let minors, rest3 = Base.List.split_n rest2 num_minors in
    let params, major_list = Base.List.split_n rest3 rec_spec.num_params in
    let major = List.hd major_list in
    let extra_args = List.tl major_list in

    (* Breaks down the constructor head and arguments *)
    let head, c_args = break_args [] major in

    match head with
    | Core_ast.Global c_name ->
        (match List.find_opt (fun c -> c.c_name = c_name) rec_spec.constructors with
        | Some c_spec ->
            (* Strip the type family indices in constructor *)
            let actual_c_args =
              if List.length c_args > rec_spec.num_indices then
                snd (Base.List.split_n c_args rec_spec.num_indices)
              else c_args
            in
            (* Return the position of the constructor corresponding to c_name *)
            let ith = match find_constructor_position c_name rec_spec.constructors with
              | Some index -> index
              | None -> failwith "Constructor not found in rec_spec"
            in
            let minor_i = List.nth minors ith in
            
            (* Substitute constructor arguments and build IHs *)
            let reduced_args =
              (* TODO: Catch exceptions when lengths don't match *)
              List.fold_right2
                (fun arg is_rec acc ->
                  if is_rec then
                    (* Generate recursive call: rec_name indices motive minors params arg *)
                    let rec_call =
                      build_app
                        (Core_ast.Global (rec_spec.ind_name ^ "rec"))
                        (indices @ [motive] @ minors @ params @ [arg])
                    in
                    arg :: rec_call :: acc
                  else
                    arg :: acc)
                actual_c_args
                c_spec.c_rec_args
                []
            in
            let step = build_app minor_i reduced_args in
            Some (build_app step extra_args)
        | None -> None)
    | _ -> None

(* Weak head reduction: note that we dliberately never reduce i and j in 
   coercions and compositions either since users can only input atoms in 
   the raw syntax *)

let rec reduce ind_env = function
  | Core_ast.Coe (i, j, Core_ast.Abs(k, Pi(x, ty1, ty2)), e) ->  
    let v1 = (create_fresh [Pi(x, ty1, ty2); e] 1).(0) in (* TODO: replace, passing vars param *)
    let i' = shift 0 1 i and j' = shift 0 1 j in
    Core_ast.Abs(v1, Core_ast.Coe (i', j', Core_ast.Abs(k, 
    (shift 2 1 (Debruijn.open_var 0
    (Core_ast.Coe (j', Local 0, Core_ast.Abs(k, shift 1 1 ty1), Local 1)) ty2))),
    (Core_ast.App(shift 0 1 e, Coe (j', i', Core_ast.Abs(k, shift 1 1 ty1), Local 0)))))

  | Core_ast.Coe (i, j, Core_ast.Abs(k, Sigma(_, ty1, ty2)), e) ->
    Pair(Coe (i, j, Abs(k, ty1), Fst e), 
    Coe (i, j, Abs(k, 
    Debruijn.open_var 0 (shift 1 1 (Coe (i, Local 0, Abs(k, ty1), Fst e))) ty2), Snd (e)))

  | Core_ast.Coe (i, j, Core_ast.Abs(k, Pathd(ty, e1, e2)), e) ->
      let v = create_fresh [ty; e1; e2; e] 3 in (* TODO: replace, passing vars param *)
      let v1 = v.(0) and v2 = v.(1) and v3 = v.(2) in
      let i' = shift 0 2 i and j' = shift 0 2 j in
      let ty' = shift 1 2 ty and e' = shift 0 2 e in
      Pabs(v1, App(Hcom(i, j, 
      Abs(v2, Coe (i', j', (Abs(k, (App(ty', Local 1)))), At(e', Local 0))), 
      Abs(v3, Coe (Local 0, j', (Abs(k, App(ty', I0()))), shift 1 1 e1)),
      Abs(v3, Coe (Local 0, j', (Abs(k, App(ty', I1()))), shift 1 1 e2))), Local 0))

  | Core_ast.Coe (i, j, e1, e2) ->
    if i = j then
      e2
    else
      let e1' = reduce ind_env e1 in
      begin match e1' with
      | Core_ast.Abs(_, e) ->
        if occurs_index 0 0 e then
          Core_ast.Coe (i, j, e1', e2)
        else
          e2  (* coercion regularity *)
      | _ ->
        Core_ast.Coe (i, j, e1', e2)
      end
  
  (* | Core_ast.Hfill (e, e1, e2) ->
    let e' = reduce ind_env e in
    let e1' = reduce ind_env e1 in
    let e2' = reduce ind_env e2 in
    Core_ast.Hfill (e', e1', e2') *)
  
  (* | Core_ast.App (Core_ast.Hfill (i, j, e, _, _), Core_ast.I0()) -> 
    reduce ind_env e *)

  | Core_ast.Hcom (i, j, e, e1, e2) -> 
    if i = j then
      e
    else
      Core_ast.Hcom (i, j, e, e1, e2)

  (* | Core_ast.App (Core_ast.Hcom (_, j, _, e1, _), Core_ast.I0()) -> 
    reduce ind_env (App (e1, j))

  | Core_ast.App (Core_ast.Hcom (_, j, _, _, e2), Core_ast.I1()) -> 
    reduce ind_env (App (e2, j)) *)

  | Core_ast.Abs (x, App (e , Local 0)) -> 
    if not (occurs_index 0 0 e) && not (Placeholder.has e) then
      reduce ind_env (shift 0 (-1) e) (* eta reduction *)
    else
      Core_ast.Abs (x, App (e , Local 0))
  
  | Core_ast.App (e1, e2) -> 
    let e1' = reduce ind_env e1 in
    (* First we attempt beta reduction *)
    begin match e1' with
    | Core_ast.Abs (_, e) ->
        reduce ind_env (beta e e2)
    | _ ->
      (* Then we attempt reduce recursor *)
      let e2' = reduce ind_env e2 in
      let full_app = Core_ast.App (e1', e2') in
      let head, args = break_args [] full_app in
      begin match head with
      | Core_ast.Global rec_name ->
          begin match Hashtbl.find_opt ind_env rec_name with
          | Some rec_spec ->
              begin match reduce_recursor rec_spec args with
              | Some reduced -> reduce ind_env reduced
              | None ->
                (* Lastly try face tube composition reduction *)
                begin match full_app with
                | App (Hcom (_, j, _, e1, _), I0()) -> reduce ind_env (App (e1, j))
                | App (Hcom (_, j, _, _, e2), I1()) -> reduce ind_env (App (e2, j))
                | _ -> full_app
                end
              end
          | None -> 
            (* Try face tube composition reduction *)
            begin match full_app with
            | App (Hcom (_, j, _, e1, _), I0()) -> reduce ind_env (App (e1, j))
            | App (Hcom (_, j, _, _, e2), I1()) -> reduce ind_env (App (e2, j))
            | _ -> full_app
            end
          end
      | _ -> 
        (* Try face tube composition reduction *)
        begin match full_app with
        | App (Hcom (_, j, _, e1, _), I0()) -> reduce ind_env (App (e1, j))
        | App (Hcom (_, j, _, _, e2), I1()) -> reduce ind_env (App (e2, j))
        | _ -> full_app
        end
      end
    end

  | Core_ast.Pair (Fst e1, Snd e2) ->
      if e1 = e2 then
        reduce ind_env e1 (* eta reduction *)
      else
        Core_ast.Pair (Fst e1, Snd e2)

  | Core_ast.Fst e ->
    let e' = reduce ind_env e in
    begin match e' with
    | Core_ast.Pair (e1 , _) -> reduce ind_env e1
    | _ -> Core_ast.Fst e'
    end

  | Core_ast.Snd e -> 
    let e' = reduce ind_env e in
    begin match e' with
    | Core_ast.Pair (_ , e2) -> reduce ind_env e2
    | _ -> Core_ast.Snd e'
    end
  
  | Core_ast.Pabs (x, At (e , Local 0)) -> 
    if not (occurs_index 0 0 e) && not (Placeholder.has e) then
      reduce ind_env (shift 0 (-1) e) (* eta reduction *)
    else
      Core_ast.Pabs (x, At (e , Local 0))

  | Core_ast.At (e1, e2) -> 
    begin
      let e1' = reduce ind_env e1 in
      match e1' with
      | Core_ast.Pabs (_ , e) ->
          reduce ind_env (beta e e2)
      | _ ->
        let e2' = reduce ind_env e2 in
        Core_ast.At (e1', e2')
    end

  | Core_ast.Type l ->
    Core_ast.Type (Core_ast.unieval l)
    
  | e -> e

let eval ind_env = reduce ind_env