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
            (* Strip constructor parameters *)
            let actual_c_args =
              if List.length c_args > rec_spec.num_params then
                snd (Base.List.split_n c_args rec_spec.num_params)
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
              List.fold_right2
                (fun arg is_rec acc ->
                  if is_rec then
                    (* Generate recursive call: rec_name params motive minors indices arg *)
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

(* Eager evaluation with locally nameless representation *)

let rec eval = function
  | Core_ast.Coe (i, j, Core_ast.Abs(k, Pi(x, ty1, ty2)), e) ->  
    let v1 = (create_fresh [Pi(x, ty1, ty2); e] 1).(0) in
    let i' = shift 0 1 (eval i) in
    let j' = shift 0 1 (eval j) in
    Core_ast.Abs(v1, Core_ast.Coe (i', j', Core_ast.Abs(k, 
    (shift 2 1 (eval (Debruijn.open_var 0
    (Core_ast.Coe (j', Local 0, Core_ast.Abs(k, shift 1 1 ty1), Local 1)) ty2)))),
    (eval (Core_ast.App(shift 0 1 e, Coe (j', i', Core_ast.Abs(k, shift 1 1 ty1), Local 0))))))

  | Core_ast.Coe (i, j, Core_ast.Abs(k, Sigma(_, ty1, ty2)), e) ->
    let i' = eval i in
    let j' = eval j in
    (* let c x = Coe (i', x, Abs(k, ty1), Fst e) in *)
    Pair(Coe (i', j', Abs(k, ty1), Fst e), 
    Coe (i', j', Abs(k, 
    eval (Debruijn.open_var 0 (shift 1 1 (Coe (i', Local 0, Abs(k, ty1), Fst e))) ty2)),
    Snd (eval e)))

  | Core_ast.Coe (i, j, Core_ast.Abs(k, Pathd(ty, e1, e2)), e) ->
      let v = create_fresh [ty; e1; e2; e] 3 in
      let v1 = v.(0) and v2 = v.(1) and v3 = v.(2) in
      let i' = shift 0 2 (eval i) in
      let j' = shift 0 2 (eval j) in
      let ty' = shift 1 2 ty and e' = shift 0 2 e in
      Pabs(v1, App(App (Hfill(
      Abs(v2, Coe (i', j', (Abs(k, (eval (App(ty', Local 1))))), eval (At(e', Local 0)))), 
      Abs(v3, Coe (Local 0, j', (Abs(k, (eval (App(ty', I0()))))), eval (shift 1 1 e1))),
      Abs(v3, Coe (Local 0, j', (Abs(k, (eval (App(ty', I1()))))), eval (shift 1 1 e2)))),
      I1()), Local 0))

  | Core_ast.Coe (i, j, e1, e2) ->
    begin
      let i' = eval i in
      let j' = eval j in
      let e2' = eval e2 in
      if i' = j' then
        e2'
      else
        let e1' = eval e1 in
        match e1' with
        | Core_ast.Abs(_, e) ->
          if occurs_index 0 0 e then
            Core_ast.Coe (i', j', e1', e2')
          else
            e2'  (* coercion regularity *)
        | _ ->
          Core_ast.Coe (i', j', e1', e2')
    end
  
  | Core_ast.Hfill (e, e1, e2) ->
    let e' = eval e in
    let e1' = eval e1 in
    let e2' = eval e2 in
    Core_ast.Hfill (e', e1', e2')
  
  | Core_ast.App (Core_ast.Hfill (e, _, _), Core_ast.I0()) -> 
    eval e

  | Core_ast.App (Core_ast.App (Core_ast.Hfill (_, e1, _), i), Core_ast.I0()) -> 
    eval (Core_ast.App(e1, i))

  | Core_ast.App (Core_ast.App (Core_ast.Hfill (_, _, e2), i), Core_ast.I1()) -> 
    eval (Core_ast.App(e2, i))
  
  | Core_ast.Abs (x, e) -> 
    begin
      let e' = eval e in
      match e' with
      | Core_ast.App (e1 , e2) ->
          begin
          match e2 with 
          | Local 0 ->
            if not (occurs_index 0 0 e1) then
              shift 0 (-1) e1 (* eta reduction *)
            else
              Core_ast.Abs (x, e')
          | _ -> Core_ast.Abs (x, e')
          end
      | _ ->
        Core_ast.Abs (x, e')
    end

  | Core_ast.App (e1, e2) -> 
    begin
      let e1' = eval e1 in
      match e1' with
      | Core_ast.Abs (_, e) ->
          eval (beta e e2)
      | _ ->
        let e2' = eval e2 in
        Core_ast.App (e1', e2')
    end

  | Core_ast.Pair (e1, e2) ->
    begin
      let e1' = eval e1 in
      let e2' = eval e2 in
      match e1', e2' with
      | Core_ast.Fst e11, Core_ast.Snd e22 ->
        if e11 = e22 then
          e11
        else
          Core_ast.Pair (e1', e2')
      | _ ->
        Core_ast.Pair (e1', e2')
    end

  | Core_ast.Fst e ->
    begin
      let e' = eval e in
      match e' with
      | Core_ast.Pair (e1 , _) -> e1
      | _ -> 
        Core_ast.Fst e'
    end

  | Core_ast.Snd e -> 
    begin
      let e' = eval e in
      match e' with
      | Core_ast.Pair (_ , e2) -> e2
      | _ -> 
        Core_ast.Snd e'
    end

  | Core_ast.Inl e ->
    let e' = eval e in
    Core_ast.Inl e'

  | Core_ast.Inr e -> 
    let e' = eval e in
    Core_ast.Inr e'

  | Core_ast.Case (e, e1, e2) -> 
    begin
      let e' = eval e in
      match e' with
      | Core_ast.Inl a -> eval (Core_ast.App (e1,a))
      | Core_ast.Inr b -> eval (Core_ast.App (e2,b))
      | _ ->
        let e1' = eval e1 in
        let e2' = eval e2 in
        Core_ast.Case (e', e1', e2')
    end

  | Core_ast.Succ e ->
    let e' = eval e in
    Core_ast.Succ e'

  | Core_ast.Natrec (e, e1, e2) -> 
    begin
      let e' = eval e in 
      match e' with
      | Core_ast.Zero() -> eval e1
      | Core_ast.Succ k -> eval (Core_ast.App (Core_ast.App (e2,k),Core_ast.Natrec(k,e1,e2)))
      | _ -> 
        let e1' = eval e1 in
        let e2' = eval e2 in
        Core_ast.Natrec (e', e1', e2')
    end

  | Core_ast.If (e, e1, e2) -> 
    begin
      let e' = eval e in
      match e' with
      | Core_ast.True() -> eval e1
      | Core_ast.False() -> eval e2
      | _ ->
        let e1' = eval e1 in
        let e2' = eval e2 in
        Core_ast.If (e', e1', e2')
    end

  | Core_ast.Let (e, e1) -> 
    begin
      let e' = eval e in
      match e' with
      | Core_ast.Star() -> eval e1
      | _ -> 
        let e1' = eval e1 in
        Core_ast.Let (e', e1')
    end

  | Core_ast.Pabs (x, e) -> 
    begin
      let e' = eval e in
      match e' with
      | Core_ast.At (e1 , e2) ->
        begin
        match e2 with 
          | Local 0 ->
            if not (occurs_index 0 0 e1) then 
              shift 0 (-1) e1 (* eta reduction *)
            else
              Core_ast.Pabs (x, e')
          | _ -> Core_ast.Pabs (x, e')
          end
      | _ ->
        Core_ast.Pabs (x, e')
    end

  | Core_ast.At (e1, e2) -> 
    begin
      let e1' = eval e1 in
      match e1' with
      | Core_ast.Pabs (_ , e) ->
          eval (beta e e2)
      | _ ->
        let e2' = eval e2 in
        Core_ast.At (e1', e2')
    end

  | Core_ast.Pi (x, e1, e2) ->
    let e1' = eval e1 in
    let e2' = eval e2 in
    Core_ast.Pi (x, e1', e2')

  | Core_ast.Sigma (x, e1, e2) ->
    let e1' = eval e1 in
    let e2' = eval e2 in
    Core_ast.Sigma (x, e1', e2')

  | Core_ast.Sum (e1, e2) ->
    let e1' = eval e1 in
    let e2' = eval e2 in
    Core_ast.Sum (e1', e2')

  | Core_ast.Pathd (e, e1, e2) -> 
    let e' = eval e in
    let e1' = eval e1 in
    let e2' = eval e2 in
    Core_ast.Pathd (e', e1', e2')

  | Core_ast.Type l ->
    Core_ast.Type (Core_ast.unieval l)
    
  | e -> e

(* Evaluation with recursors of inductive families *)

let eval_only_rec ind_env = function
  | App (e1, e2) ->
    let e1' = eval e1 in
    let e2' = eval e2 in
        let full_app = Core_ast.App (e1', e2') in
        let head, args = break_args [] full_app in
        (match head with
        | Core_ast.Global namerec ->
            let name = String.sub namerec 0 (String.length namerec - 3) in 
            (match Hashtbl.find_opt ind_env name with
            | Some rec_spec ->
                (match reduce_recursor rec_spec args with
                | Some reduced -> reduced
                | None -> full_app)
            | None -> full_app)
        | _ -> full_app)
  | e -> e