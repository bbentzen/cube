(**
  (c) Copyright 2019 Bruno Bentzen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Desc: This module contains the small trusted kernel plus type inference.
        The elaborator performs the endpoint ε-reductions for dependent paths.
        The unifier implements the boundary separation rule
 **)

open Basis
open Context
open Ast
open Eval

let st = Constraints.empty ()

let solve_meta_application args vars body = function
  | Meta n ->
    let rec build_lam vars body = function
      | [] -> body
      | _ :: args -> 
        let v1 = Expr.init_fresh vars in
        Lam (v1, build_lam (vars + 1) (Expr.shift 1 0 body) args)
    in
    if Placeholder.has_placeholder_name n body then None else 
      Some (build_lam vars body args)
  | _ -> None

(* Checks whether the type of a given expression is the given type *)

let rec elaborate global ind_env ctx lvl sl ty  vars = function
  | Global x ->
    begin match Global.var_type x ctx with
    | Ok xty ->
      let ty = eval ind_env ty in
      let c = Global.check_var_ty x ty ctx in
      let h = Placeholder.is ty in 
      let h' = Placeholder.is xty in 
      let d = Global.is_declared x ctx in
      begin match c, h, h', d with
      | true , _, _ , _ | _ , _, true , _ -> Ok (Global x, ty, sl)
      | _ , true, _ , _ -> Ok (Global x, xty, sl)
      | false , false, false , true ->
        let h1 = Placeholder.generate () in
        begin match elaborate global ind_env ctx lvl sl h1 vars xty with
        | Ok (_, tTy', sa) ->
          let u = unify global ind_env ctx lvl sl vars (eval ind_env ty, eval ind_env xty, tTy') true in
          begin match u with
          | Ok s -> 
            Ok (Global x, s, sl) 
          | Error (_, msg) -> Error (sa, Msg.var_type_mismatch x xty ty msg)
          end
        | Error (sa, msg) -> Error (sa, Msg.var_error x msg)
        end
      | false, false, false, false -> 
        begin match Env.unfold x global with
        | Ok (_, xty) ->
          let h1 = Placeholder.generate () in
          begin match elaborate global ind_env ctx lvl sl h1  vars xty with
          | Ok (_, tTy', sa) ->
            let u = unify global ind_env ctx lvl sl  vars (eval ind_env xty, eval ind_env ty, tTy') true in
            begin match u with
            | Ok s -> Ok (Global x, s, sl) (* runs faster when not body *)
            | _ -> Error (sa, Msg.var_type_mismatch_2 x xty ty)
            end
          | Error (sa, msg) -> Error (sa, Msg.var_error x msg)
          end
        | Error msg -> Error (sl, Msg.var_error x msg)
        end
      end
    | Error _ -> Error (sl, Msg.undeclared x)
    end
    
  | I0() ->
    begin match ty with
    | Int() -> Ok (I0(), Int(), sl)
    | Meta _ -> Ok (I0(), Int(), sl)
    | _ -> Error (sl, Msg.i0_error ty)
    end
  
  | I1() ->
    begin match ty with
    | Int() -> Ok (I1(), Int(), sl)
    | Meta _ -> Ok (I1(), Int(), sl)
    | _ -> Error (sl, Msg.i1_error ty)
    end

  | Lam (x, e) ->
    let e = eval ind_env e in
    let ty = eval ind_env ty in
    begin match ty with
    | Pi (_, ty1, ty2) ->
      let v1 = Expr.mk_fresh x ctx in
      let e' = Expr.open_var 0 (Global v1) e in
      let ty2' = Expr.open_var 0 (Global v1) ty2 in
      let elab = elaborate global ind_env ((v1, ty1, true) :: ctx) lvl sl ty2'  (vars+1) e' in
      begin match elab with
      | Ok (e', ty2', sa) -> 
        Ok (Lam (v1, Expr.close_bound v1 e'), Pi (v1, ty1, Expr.close_bound v1 ty2'), sa)
      | Error (sa, msg) -> Error (sa, msg)
      end
    | Meta _ ->
      let h1 = Placeholder.generate () in
      let h2 = Placeholder.generate () in
      elaborate global ind_env ctx lvl sl (Pi(x, h1, h2))  vars (Lam (x, e))
    | _ -> 
      Error (sl, Msg.lam_error x e ty)
    end

  | App (e1, e2) ->
    (* If the head expression is a recursor try to infer the motive *)
    let ty = eval ind_env ty in
    let head, args = Eval.break_args [] (App (e1, e2)) in
    let rec_env, cons_env = ind_env in 
    begin match Infer.rec_motive_idx elaborate global ind_env ctx lvl sl vars rec_env ty args head with
    | Some res ->
      elaborate global ind_env ctx lvl sl ty  vars res
    | None ->
      (* If the head expression is a constructor try to infer indices *)
      begin match Infer.constr_indices cons_env ty args head with
      | Some res ->
        elaborate global ind_env ctx lvl sl ty  vars res
      | None ->
        (* Otherwise infer the type of e1 and check its evaluated domain against e2 *)
        let h1 = Placeholder.generate () in
        let v1 = Expr.init_fresh vars in
        let h2 = Placeholder.generate () in
        let elab1 = elaborate global ind_env ctx lvl sl (Pi(v1, h1, h2)) (vars+1) e1 in
        begin match elab1 with
        | Ok (e1', Pi(_, ty1, ty2), sa1) ->
          (* Evaluates the inferred domain before type checking *)
          let ty1' = eval ind_env ty1 in
          let h3 = Placeholder.generate () in
          let elab2 = elaborate global ind_env ctx lvl sl ty1' (vars+1) e2 in
          begin match elab2 with
          | Ok (e2', _, sa2) ->
            (* Otherwise unify both types possibly lifting the universe levels *)
            let ty2' = eval ind_env (Expr.open_var 0 e2' ty2) in
            let u = unify global ind_env ctx lvl sl (vars+1) (ty, ty2', h3) true in
            begin match u with
            | Ok _ -> 
              Ok (App (e1', e2'), ty2', Stack.append sa1 sa2)
            | Error (_, msg) ->
              Error (Stack.append sa1 sa2, Msg.app_fail_1 e2' ty1' msg)
            end
          | Error (sa2, msg) -> 
            Error (Stack.append sa1 sa2, Msg.app_fail_2 e2 ty1' msg)
          end
        | Ok (e1', ty1', sa1) -> 
          begin match elaborate global ind_env ctx lvl sl h1 (vars+1) e2 with
          | Ok (e2', ty1, sa2) ->
            Constraints.add st {
            lhs = (Pi(v1, ty1, h2)); 
            rhs = ty1'; 
            cty = Type(Var "?_"); 
            clift = true };
            let ty2' = eval ind_env (Expr.open_var 0 e2' h2) in
            (* Delay unification *)
            Ok (App (e1', e2'), ty2', Stack.append sa1 sa2)
          | Error (sa2, msg) -> 
            Error (Stack.append sa1 sa2, Msg.app_fail_2 e2 ty1' msg)
          end
          (* Error (sa1, Msg.app_wrong_ty1 e1' (Pi(v1, h1, h2)) ty1') *)
        | Error (sa, msg) -> 
          Error (sa, Msg.app_wrong_ty2 e1 msg)
        end
      end
    end
  
  | Abort e ->
    begin match elaborate global ind_env ctx lvl sl (Void()) vars e with
    | Ok (e', _, sa) -> Ok (Abort e', ty, sa)
    | Error (sa, msg) -> Error (sa, Msg.void_error e msg)
    end
  
  | Coe(i, j, ety, e) ->
    let h0 = Placeholder.generate () in
    let elabi = elaborate global ind_env ctx lvl sl (Int())  vars i in
    let elabj = elaborate global ind_env ctx lvl sl (Int())  vars j in
    let tyi_expr = eval ind_env (App(ety, i)) in
    let tyj_expr = eval ind_env (App(ety, j)) in
    let elabti = elaborate global ind_env ctx lvl sl h0  vars tyi_expr in
    let elabtj = elaborate global ind_env ctx lvl sl h0  vars tyj_expr in
    begin match elabi, elabj, elabti, elabtj with
    | Ok (i', _, _), Ok (j', _, _), Ok (tyi, eTy, sat), Ok (tyj, _, _) ->
      let e' = eval ind_env e in
      let elab = elaborate global ind_env ctx lvl sl (eval ind_env tyi)  vars e' in
      let elabt = elaborate global ind_env ctx lvl sl h0 vars ty in
      begin match elab, elabt with
      | Ok (e', _, sa), Ok (ty', _, sat') ->
        let u = unify global ind_env ctx lvl sl  vars (eval ind_env tyj, eval ind_env ty', eTy) false in
        begin match u with
        | Ok tty ->
          Ok (Coe (i', j', eval ind_env ety, e'), tty, Stack.lappend sa sat sat')
        | Error (_, msg) -> Error (Stack.lappend sa sat sat', Msg.coercion_error_1 tyj ty' eTy i j ety e ty msg)
        end
      | Error (sa, msg), _ -> Error (sa, Msg.coercion_error_2 e tyi msg)
      | _, Error (sa, msg) -> Error (sa, Msg.coercion_error_3 ty msg)
      end
    | Error (sa, msg), _, _, _ -> Error (sa, Msg.coercion_error_i i msg)
    | _, Error (sa, msg), _, _ -> Error (sa, Msg.coercion_error_i j msg)
    | _, _, Error (sa, msg), _ -> Error (sa, Msg.coercion_error_ty tyi_expr i msg)
    | _, _, _, Error (sa, msg) -> Error (sa, Msg.coercion_error_ty tyj_expr j msg)
    end
  
  | Local index -> Error (sl, Msg.unexpected index ty ctx)

  | Hcom(i1, j1, e, e1, e2) ->
    begin match ty with
    | Pi(k, int, ty') ->
      let int = eval ind_env int in
      let ty' = eval ind_env ty' in
      begin match int, ty' with
      | Int(), ty' ->
        (* Determine the target type for the lid and tubes *)
        let ty0 = Expr.open_var 0 (I0()) ty' in
        let ty1 = Expr.open_var 0 (I1()) ty' in
        let jty = Pi(k, Int(), ty') in
        let jty0 = Pi(k, Int(), ty0) in
        let jty1 = Pi(k, Int(), ty1) in
        (* Typecheck the lid and tubes *)
        let elab = elaborate global ind_env ctx lvl sl jty  vars e in
        let elab1 = elaborate global ind_env ctx lvl sl jty0 vars e1 in  (* subst i0 *)
        let elab2 = elaborate global ind_env ctx lvl sl jty1  vars e2 in  (* subst i1 *)
        begin match elab, elab1, elab2 with
        | Ok (e', ety, sa), Ok (e1', e1ty, sa1), Ok (e2', e2ty, sa2) ->
          (* Typecheck the endpoints of the lid *)
          let elabi0 = elaborate global ind_env ctx lvl sl ty0  vars (eval ind_env (App(e', I0()))) in
          let elabi1 = elaborate global ind_env ctx lvl sl ty1  vars (eval ind_env (App(e', I1()))) in
          (* Typecheck the i face of the tubes *)
          let elab1i0 = elaborate global ind_env ctx lvl sl ty0  vars (eval ind_env (App(e1', i1))) in
          let elab2i0 = elaborate global ind_env ctx lvl sl ty1  vars (eval ind_env (App(e2', i1))) in
          begin match elabi0, elabi1, elab1i0, elab2i0 with
          | Ok (ei0, _, _), Ok (ei1, _, _), Ok (e1i0, _, _), Ok (e2i0, _, _) ->
            (* Validate the composition scenario by matching the i-corners of the square *)
            let u1 = unify global ind_env ctx lvl sl vars (eval ind_env ei0, e1i0, ty0) false in
            let u2 = unify global ind_env ctx lvl sl vars (eval ind_env ei1, e2i0, ty1) false in
            begin match u1, u2 with
            | Ok _, Ok _ ->
              let return x = Ok (Hcom(i1, j1, e', e1', e2'), x, Stack.lappend sa sa1 sa2) in
              if not (Placeholder.has_placeholder ty) then
                return ty
              else if not (Placeholder.has_placeholder ety) then
                return (Pi (k, Int(), ety))
              else if not (Placeholder.has_placeholder e1ty) then
                return (Pi (k, Int(), e1ty))
              else if not (Placeholder.has_placeholder e2ty) then
                return (Pi (k, Int(), e2ty))
              else
                return ty
            | Error (_, msg), _ -> Error (Stack.lappend sa sa1 sa2, Msg.lid_unify ind_env ei0 i1 e1i0 msg)
            | _, Error (_, msg) -> Error (Stack.lappend sa sa1 sa2, Msg.tube_i1_unify ind_env ei1 i1 e2i0 msg)
            end
            
          | Error (sa', msg), _, _, _ -> Error (Stack.append4 sa' sa sa1 sa2, Msg.lid_i0 ind_env i1 j1 e' e1' e2' ty' msg)
          | _, Error (sa', msg), _, _ -> Error (Stack.append4 sa' sa sa1 sa2, Msg.lid_i1 ind_env i1 j1 e' e1' e2' ty' msg)
          | _, _, Error (sa', msg), _ -> Error (Stack.append4 sa' sa sa1 sa2, Msg.tube_i0 ind_env i1 j1 e' e1' e2' ty' msg)
          | _, _, _, Error (sa', msg) -> Error (Stack.append4 sa' sa sa1 sa2, Msg.tube_i1 ind_env i1 j1 e' e1' e2' ty' msg)
          end
        | Error (sa, msg), _, _ | _, Error (sa, msg), _ | _, _, Error (sa, msg) -> Error (sa, Msg.hcom_error msg)
        end
      
      | Meta _, Meta _ -> 
        (* Infer the type of the lid and the tubes *)
        let h0 = Placeholder.generate () in
        let elab = elaborate global ind_env ctx lvl sl (Pi("v1", Int(), h0))  vars e in
        let elab1 = elaborate global ind_env ctx lvl sl (Pi("v1", Int(), h0))  vars e1 in
        let elab2 = elaborate global ind_env ctx lvl sl (Pi("v1", Int(), h0))  vars e2 in
        begin match elab, elab1, elab2 with
        | Ok (e', ety, ss), Ok (e1', _, _), Ok (e2', _, _) ->
          (* Synthesize the face types based on what was inferred *)
          begin match eval ind_env ety with
          | Pi(i, Int(), ty') ->
            let ty0 = Expr.open_var 0 (I0()) ty' in
            let ty1 = Expr.open_var 0 (I1()) ty' in
            let elabi0 = elaborate global ind_env ctx lvl sl ty0  vars (eval ind_env (App(e', I0()))) in
            let elabi1 = elaborate global ind_env ctx lvl sl ty1  vars (eval ind_env (App(e', I1()))) in
            begin match elabi0, elabi1 with
            | Ok (ei0, _, sa), Ok (ei1, _, _) ->
              (* Typecheck the i face of the tubes *)
              let elab1i0 = elaborate global ind_env ctx lvl sl ty0  vars (eval ind_env (App(e1', i1))) in
              let elab2i1 = elaborate global ind_env ctx lvl sl ty1  vars (eval ind_env (App(e2', i1))) in
              begin match elab1i0, elab2i1 with
              | Ok (e1i0, _, sa1), Ok (e2i0, _, sa2) ->
                let u1 = unify global ind_env ctx lvl sl  vars (eval ind_env ei0, e1i0, ty0) false in
                let u2 = unify global ind_env ctx lvl sl  vars (eval ind_env ei1, e2i0, ty1) false in
                begin match u1, u2 with
                | Ok _, Ok _ ->
                  Ok (Hcom(i1, j1, e', e1', e2'), Pi(i, Int(), ty'), Stack.lappend sa sa1 sa2)
                | Error (_, msg), _ ->
                  Error (Stack.lappend sa sa1 sa2, Msg.lid_unify ind_env ei0 i1 e1i0 msg)
                | _, Error (_, msg) -> 
                  Error (Stack.lappend sa sa1 sa2, Msg.tube_i1_unify ind_env ei1 i1 e2i0 msg)
                end
              | Error (sa, msg), _ -> Error (sa, Msg.tube_i0_meta ind_env i1 j1 e' e1' e2' ty0 msg)
              | _, Error (sa, msg) -> Error (sa, Msg.tube_i1_meta ind_env i1 j1 e' e1' e2' ty0 msg)
              end
            | Error (sa', msg), _ -> Error (Stack.append ss sa', Msg.lid_meta ind_env e' ety e1' e2' ty' msg)
            | _, Error msg -> Error msg
            end
          | _ -> Error (sl, Msg.lid_unexpected e ety)
          end
        | Error msg, _, _ | _, Error msg, _ | _, _, Error msg -> 
          Error msg
        end
      | _, _ -> Error (sl, Msg.hcom_unexpected_1 i1 j1 e e1 e2 k int ty')
      end
    | ty -> Error (sl, Msg.hcom_unexpected_2 i1 j1 e e1 e2 ty)
    end

  | Pabs (i, e) ->
    let e = eval ind_env e in
    let ty = eval ind_env ty in
    let h0 = Placeholder.generate () in
    let elabt = elaborate global ind_env ctx lvl sl h0  vars ty in
    begin match elabt with
    | Ok (Pathd (Meta n, e1, e2), _, _) ->
      let v1 = Expr.mk_fresh i ctx in
      let h0 = Placeholder.generate () in
      let ei = Expr.open_var 0 (Global v1) e in
      let elab = elaborate global ind_env ((v1, Int(), true) :: ctx) lvl sl (Meta n)  (vars+1) ei in
      begin match elab with
      | Ok (e', _, sa) ->
        let e_closed = Expr.close_bound v1 e' in
        let ei0 = Expr.open_var 0 (I0()) e_closed in
        let ei1 = Expr.open_var 0 (I1()) e_closed in
        let elab1 = elaborate global ind_env ((v1, Int(), true) :: ctx) lvl sl h0  (vars+1) ei0 in
        let elab2 = elaborate global ind_env ((v1, Int(), true) :: ctx) lvl sl h0  (vars+1) ei1 in
        begin match elab1, elab2 with
        | Ok (ei0, tyi0, _), Ok (ei1, tyi1, _) ->
          (* Proceed with unification *)
          let u1 = unify global ind_env ctx lvl sl  (vars+1) (eval ind_env ei0, eval ind_env e1, tyi0) false in
          let u2 = unify global ind_env ctx lvl sl  (vars+1) (eval ind_env ei1, eval ind_env e2, tyi1) false in
          begin match u1, u2 with
          | Ok ui0, Ok ui1 ->
            let v2 = Expr.init_fresh vars in
            let ty' = Expr.fullsubst 0 (I0()) (Global v2) true tyi0 in
            let ty'' = Expr.fullsubst 0 (I1()) (Global v2) true tyi1 in
            let elabTy = elaborate global ind_env ctx lvl sl h0  (vars+2) ty in
            begin match elabTy with
            | Ok (_, tTy, _) ->
              let u = unify global ind_env ctx lvl sl  (vars+2) (ty', ty'', tTy) false in
              begin match u with
              | Ok st -> Ok (Pabs (v1, e_closed), Pathd (Lam(v2, st), ui0, ui1), sa)
              | Error (_, msg) -> Error (sa, Msg.pabs_unify_generic msg)
              end
            | Error (sa', msg) -> Error (Stack.append sa sa', Msg.pabs_error msg)
            end
          | _ , Ok _ -> Error (sa, Msg.pabs_unify_i0 v1 e1 ei0 e e' ty ctx) 
          | _ -> Error (sa, Msg.pabs_unify_i1 v1 e2 ei1 e e' ty ctx)
          end
        | Error (_, msg), _| _, Error (_, msg) -> Error (sa, Msg.pabs_syn msg)
        end
      | Error (sa, msg) -> Error (sa, Msg.pabs_syn msg)
      end
    | Ok (Pathd (ty1, e1, e2), _, _) ->
      let v1 = Expr.mk_fresh i ctx in
      let ei = Expr.open_var 0 (Global v1) e in
      let ty1' = eval ind_env (App(ty1, Global v1)) in
      let elab = elaborate global ind_env ((v1, Int(), true) :: ctx) lvl sl ty1'  (vars+1) ei in
      begin match elab with
      | Ok (e', _, saa) ->
        let e_closed = Expr.close_bound v1 e' in
        let ei0 = eval ind_env (Expr.open_var 0 (I0()) e_closed) in
        let ei1 = eval ind_env (Expr.open_var 0 (I1()) e_closed) in
        let elab1 = elaborate global ind_env ctx lvl sl (eval ind_env (App(ty1, I0())))  (vars+1) ei0 in
        let elab2 = elaborate global ind_env ctx lvl sl (eval ind_env (App(ty1, I1())))  (vars+1) ei1 in
        begin match elab1, elab2 with
        | Ok (ei0, tyi0, _), Ok (ei1, tyi1, _) ->
          let ei0' = eval ind_env ei0 and e1' = eval ind_env e1 in
          let ei1' = eval ind_env ei1 and e2' = eval ind_env e2 in
          let u1 = unify global ind_env ctx lvl sl  vars (ei0', e1', tyi0) false in
          let u2 = unify global ind_env ctx lvl sl  vars (ei1', e2', tyi1) false in
          begin match u1, u2 with
          | Ok ui0, Ok ui1 -> 
            Ok (Pabs (v1, e_closed), Pathd (ty1, ui0, ui1), saa)
          | Error ((s,s'), msg) , Ok _ ->
            begin match s, s' with
            | At(s',I0()), s | s, At(s',I0()) ->
              let h1 = Placeholder.generate () in
              let elab0 = elaborate global ind_env ctx lvl sl h1  vars s' in
              begin match elab0 with
              | Ok (_, Pathd(sty, sa, _), _) ->
                let u = unify global ind_env ctx lvl sl  vars (s, sa, eval ind_env (App(sty, I0()))) false in
                begin match u with
                | Ok _ -> Ok (Pabs (v1, e_closed), Pathd (ty1, ei0, ei1), saa)
                | Error (_, msg) -> Error (saa, Msg.pabs_unify_i0_2 v1 e1 ei0 e' ty ctx msg)
                end
              | _ -> Error (saa, Msg.pabs_unify_i0_2 v1 e1 ei0 e' ty ctx msg)
              end
            | _ -> Error (saa, Msg.pabs_unify_i0_3 v1 e1 ei0 e' ty ctx msg)
            end
          | _ , Error ((s,s'), msg) ->
            begin match s, s' with
            | At(s',I1()), s | s, At(s',I1()) ->
              let h1 = Placeholder.generate () in
              let elab0 = elaborate global ind_env ctx lvl sl h1  vars s' in
              begin match elab0 with
              | Ok (_, Pathd(sty,_,sb), _) ->
                let u = unify global ind_env ctx lvl sl  vars (s, sb, eval ind_env (App(sty, I1()))) false in
                begin match u with
                | Ok _ -> 
                  Ok (Pabs (i, e_closed), Pathd (ty1, ei0, ei1), saa)
                | Error (_, msg) -> Error (saa, Msg.pabs_unify_i1_2 v1 e2 ei1 e' ty ctx msg)
                end
              | _ -> Error (saa, Msg.pabs_unify_i1_3 v1 e2 ei1 e' ty ctx msg)
              end
            | _ ->
              Error (saa, Msg.pabs_unify_i1_4 v1 e2 e2' ei1 ei1' e' ty ctx msg)
            end
          end
        | Error (_, msg), _ -> Error (saa, Msg.pabs_i0_ty ind_env v1 e ty e' ty1 msg)
        | _, Error (_, msg) -> Error (saa, Msg.pabs_i1_ty ind_env v1 e ty e' ty1 msg)
        end
      | Error (sa, msg) -> Error (sa, Msg.pabs_ty_fail ei ty1' msg)
      end
    | Ok (Meta _, _, _) ->
      let h1 = Placeholder.generate () in
      let ei0 = Expr.open_var 0 (I0()) e in
      let ei1 = Expr.open_var 0 (I1()) e in
      let elab0 = elaborate global ind_env ctx lvl sl h1 vars ei0 in
      let elab1 = elaborate global ind_env ctx lvl sl h1 vars ei1 in
      begin match elab0, elab1 with
      | Ok (_, tyi0, _), Ok (_, tyi1, _) ->
        let v1 = Expr.init_fresh vars in
        let ty' = Expr.fullsubst 0 (I0()) (Global v1) true tyi0 in
        let ty'' = Expr.fullsubst 0 (I1()) (Global v1) true tyi1 in
        begin match elaborate global ind_env ctx lvl sl h1  (vars+1) ty' with
        | Ok (ty', tTy', _) ->
          let u = unify global ind_env ctx lvl sl  (vars+1) (ty', ty'', tTy') false in
          begin match u with
          | Ok st ->
            elaborate global ind_env ctx lvl sl (Pathd(Lam(v1,st), ei0, ei1))  (vars+1) (Pabs (i, e))
          | Error (_, msg) -> Error (sl, Msg.pabs_meta_unify ty' ty'' msg)
          end
        | Error msg -> Error msg
        end
      | Error msg, _ | _, Error msg -> Error msg
      end
    | Ok (ty', _, sa) -> Error (sa, Msg.pabs_unexpected i e ty ty')
    | Error (sa, msg) -> Error (sa, Msg.pabs_not_ty ind_env ty msg)
    end
  
  | At (e1, e2) ->
    let h1 = Placeholder.generate () in
    let h2 = Placeholder.generate () in
    let h3 = Placeholder.generate () in
    let elab1 = elaborate global ind_env ctx lvl sl (Pathd(h1, h2, h3))  vars e1 in
    let elab2 = elaborate global ind_env ctx lvl sl (Int())  vars e2 in
    begin match elab1, elab2 with
    | Ok (e1', ty1', sa1), Ok (e2', _, sa2) ->
      begin match ty1' with
      | Pathd (ty', a, b) ->
        if e2' = I0() then (* TODO: better as pattern matching *)
          match a, ty' with
          | Meta _, Lam(_, ty') -> (* unify ty' and ty*)
            Ok (At (e1', I0()), Expr.open_var 0 (I0()) ty', Stack.append sa1 sa2)
          | Meta _, Meta _ -> 
            Ok (At (e1', I0()), ty, Stack.append sa1 sa2)
          | Meta _, ty' -> 
            Ok (At (e1', I0()), App(ty', I0()), Stack.append sa1 sa2)
          | _ -> 
            elaborate global ind_env ctx lvl sl ty  vars a
        else if e2' = I1() then
          match b, ty' with
          | Meta _, Lam(_, ty') -> 
            Ok (At (e1', I1()), Expr.open_var 0 (I1()) ty', Stack.append sa1 sa2)
          | Meta _, Meta _ -> 
            Ok (At (e1', I1()), ty, Stack.append sa1 sa2)
          | Meta _, ty' -> 
            Ok (At (e1', I1()), App(ty', I1()), Stack.append sa1 sa2)
          | _ -> 
            elaborate global ind_env ctx lvl sl ty  vars b
        else
          begin match ty' with
          | Lam(_, ty') ->
            let ty2' = Expr.open_var 0 e2' ty' in
            let elabTy = elaborate global ind_env ctx lvl sl h1  vars ty2' in
            begin match elabTy with
            | Ok (_, tTy, _) ->
              let u = unify global ind_env ctx lvl sl  vars (ty2', ty, tTy) false in
              begin match u with
              | Ok tty -> Ok (At (e1', e2'), tty, Stack.append sa1 sa2)
              | _ -> Error (Stack.append sa1 sa2, Msg.at_unify ty2' ty)
              end
            | Error msg -> Error msg
            end
            
          | _ -> 
            begin match ty with
            | App(ty, i) ->
              let elabTy = elaborate global ind_env ctx lvl sl h1  vars ty' in
              begin match elabTy with
              | Ok (_, tTy, _) ->
                let u = unify global ind_env ctx lvl sl  vars (ty', ty, tTy) false in
                begin match u, e2 = i with 
                | Ok tty, true -> 
                  Ok (At (e1', e2'), App(tty, i), Stack.append sa1 sa2)
                | _ -> Error (Stack.append sa1 sa2, Msg.at_unify ty' ty)
                end
              | Error msg -> Error msg
              end
            | ty ->
              let elabTy = elaborate global ind_env ctx lvl sl h1  vars ty' in
              begin match elabTy with
              | Ok (_, tTy, _) ->
                let u = unify global ind_env ctx lvl sl  vars (ty', ty, tTy) false in
                begin match u with
                | Ok tty -> 
                  Ok (At (e1', e2'), tty, Stack.append sa1 sa2) 
                | _ -> 
                  Error (Stack.append sa1 sa2, Msg.at_unify ty' ty)
                end
              | Error msg -> Error msg
              end
            end
          end
      | _ -> Error (Stack.append sa1 sa2, Msg.path_mismatch e1' ty1')
      end
    | Error msg, _ | _, Error msg -> Error msg
    end

  | Pi(x, ty1, ty2) ->
    let ty1 = eval ind_env ty1 in
    let h1 = Placeholder.generate () in
    let elab1 = elaborate global ind_env ctx lvl sl h1  vars ty1 in
    let ty2 = eval ind_env ty2 in
    let ty2' = (Expr.open_var 0 (Global x) ty2) in
    let elab2 = elaborate global ind_env ((x, ty1, true) :: ctx) lvl sl h1  vars ty2'
    in
    begin match elab1, elab2 with
    | Ok (ty1', Type n1, sa1), Ok (ty2', Type n2, sa2) -> 
      let max = Level.reduce (Max(n1, n2)) in
      begin match ty with
      | Type (Var par) when Level.is_arbitrary_string par ->
        (* Synthesize type levels placeholder *)
        Ok (Pi(x, ty1', Expr.close_bound x ty2'), Type (Suc(max)), Stack.append sa1 sa2)
      | Type m ->
        (* Check if levels are compatible *)
        if Level.leq max m then 
          Ok (Pi(x, ty1', Expr.close_bound x ty2'), Type m, Stack.append sa1 sa2)
        else 
          Error (Stack.append sa1 sa2, Msg.pi_universe_1 x ty1 ty2 max m)
      | Meta n ->
        Hashtbl.add Data.meta_store n { Data.solution = Type max};
        Ok (Pi(x, ty1', Expr.close_bound x ty2'), Type max, Stack.append sa1 sa2)
      | _ -> Error (Stack.append sa1 sa2, Msg.pi_universe_2 x ty1 ty2 ty)
      end
    (* Store these Ok'd metas? *)
    | Ok (ty1', Type n, sa), Ok (ty2', Meta _, _) 
    | Ok (ty1', Meta _, sa), Ok (ty2', Type n, _) -> 
      begin match ty with
      | Type m ->
        if Level.leq n m then 
          Ok (Pi(x, ty1', Expr.close_bound x ty2'), Type m, sa) 
        else 
          Error (sa, Msg.pi_universe_1 x ty1 ty2 n m)
      | Meta k -> 
        Hashtbl.add Data.meta_store k { Data.solution = Type n}; 
        Ok (Pi(x, ty1', Expr.close_bound x ty2'), Type n, sa)
      | _ -> 
        Error (sa, Msg.pi_universe_2 x ty1 ty2 ty)
      end
    
    | Ok (ty1', Type n, sa), Ok (Meta k, _, _) -> 
      begin match ty with
      | Type m ->
        if Level.leq n m then 
          Ok (Pi(x, ty1', Meta k), Type m, sa) 
        else 
          Error (sa, Msg.pi_universe_1 x ty1 ty2 n m)
      | Meta l ->
        Hashtbl.add Data.meta_store l { Data.solution = Type n}; 
        Ok (Pi(x, ty1', Meta k), Type n, sa) (* TODO: hole might live in a higher universe *)
      | _ -> 
        Error (sa, Msg.pi_universe_2 x ty1 ty2 ty)
      end
    | Ok (Meta k, _, _), Ok (ty2', Type n, sa) -> 
      begin match ty with
      | Type m ->
        if Level.leq n m then 
          Ok (Pi(x, Meta k, Expr.close_bound x ty2'), Type m, sa) 
        else 
          Error (sa, Msg.pi_universe_1 x ty1 ty2 n m)
      | Meta l ->
        Hashtbl.add Data.meta_store l { Data.solution = Type n}; 
        Ok (Pi(x, Meta k, Expr.close_bound x ty2'), Type n, sa) (* TODO: hole might have live in a higher universe *)
      | _ ->
        Error (sa, Msg.pi_universe_2 x ty1 ty2 ty)
      end
    | Ok (Meta k1, _, _), Ok (Meta k2, _, _) ->
      begin match ty with
      | Type m -> Ok (Pi(x, Meta k1, Meta k2), Type m, sl) 
      | Meta k -> Ok (Pi(x, Meta k1, Meta k2), Meta k, sl)
      | _ -> Error (sl, Msg.pi_universe_2 x ty1 ty2 ty)
      end
    
    | Ok (_, Type _, sa), Error (sb, msg) -> Error (Stack.append sa sb, Msg.pi_codomain ind_env ty2' msg)
    | _, Error (sb, msg) -> Error (sb, Msg.pi_codomain ind_env ty2' msg)
    | Error (sa, msg), _ -> 
      Error (sa, Msg.pi_domain ind_env ty1 msg)
    | Ok (ty1', u1, _), Ok (ty2', u2, _) -> 
      Error (sl, Msg.pi_unexpected x ty1 ty2 ty ty1' u1 ty2' u2)
    end
  
  | Int() ->
    let ty = eval ind_env ty in
    begin match ty with
    | Type m -> Ok (Int(), Type m, sl)
    | Meta k ->
      Hashtbl.add Data.meta_store k { Data.solution = Type (Num 0)}; 
      Ok (Int(), Type (Num 0), sl)
    | _ -> Error (sl, Msg.interval ty)
    end

  | Void() ->
    let ty = eval ind_env ty in
    begin match ty with
    | Type m -> Ok (Void(), Type m, sl)
    | Meta k -> 
      Hashtbl.add Data.meta_store k { Data.solution = Type (Num 0)}; 
      Ok (Void(), Type (Num 0), sl)
    | _ -> Error (sl, Msg.void_ty ty)
    end

  | Pathd(ty1, e1, e2) ->
    let h1 = Placeholder.generate () in
    let ty = eval ind_env ty in
    (* First consider the inference case: the type line is a placeholder *)
    begin match ty1 with
    (* Subcase 1: dependent type placeholder *)
    | Meta n ->
      begin match e1, e2 with
      | Meta n1, Meta n2 ->
          begin match ty with
          | Type m -> Ok (Pathd(Meta n, Meta n1, Meta n2), Type m, sl)
          | Meta m ->
            Ok (Pathd(Meta n, Meta n1, Meta n2), Meta m, sl)
          | _ -> Error (sl, Msg.not_a_type ty)
          end
      | _ ->
        (* Neither endpoint is a placeholder *)
        let elab1 = elaborate global ind_env ctx lvl sl h1  vars e1 in
        let elab2 = elaborate global ind_env ctx lvl sl h1  vars e2 in
        begin match elab1, elab2 with
        | Ok (e1', tye1, sa1), Ok (e2', tye2, sa2) ->
          let tye1 = eval ind_env tye1 in
          let tye2 = eval ind_env tye2 in
          begin match ty, tye1, tye2 with
          (* Target type has been specified *)
          | Type m, tye1, Meta _ ->
            let v1 = Expr.init_fresh vars in
            let tyei = Pi(v1, Int(), Expr.fullsubst 0 (I0()) (Local 0) true tye1) in
            Ok (Pathd(tyei, e1', e2'), Type m, Stack.append sa1 sa2)
          | Type m, _ , tye2 -> 
            let v1 = Expr.init_fresh vars in
            let tyei = Pi(v1, Int(), Expr.fullsubst 0 (I1()) (Local 0) true tye2) in
            Ok (Pathd(tyei, e1', e2'), Type m, Stack.append sa1 sa2)
          (* Target type is a placeholder *)
          | Meta _, tye1, Meta _ ->
            let v1 = Expr.init_fresh vars in
            let tyei = Pi(v1, Int(), Expr.fullsubst 0 (I0()) (Local 0) true tye1) in
            let h2 = Placeholder.generate () in
            begin match elaborate global ind_env ctx lvl sl h2  vars tye1 with
            | Ok (_, tTye1, _) -> Ok (Pathd(tyei, e1', e2'), tTye1, Stack.append sa1 sa2)
            | Error (_, msg) -> Error (Stack.append sa1 sa2, Msg.not_a_type_2 tye1 msg)
            end
          | Meta _, _, tye2 -> 
            let v1 = Expr.init_fresh vars in
            let tyei = Pi(v1, Int(), Expr.fullsubst 0 (I1()) (Local 0) true tye2) in
            let h2 = Placeholder.generate () in
            begin match elaborate global ind_env ctx lvl sl h2  vars tye2 with
            | Ok (_, tTye2, _) -> Ok (Pathd(tyei, e1', e2'), tTye2, Stack.append sa1 sa2)
            | Error (_, msg) -> Error (Stack.append sa1 sa2, Msg.not_a_type_2 tye1 msg)
            end
          | _ -> Error (Stack.append sa1 sa2, Msg.not_a_type ty)
          end
        | _ -> Error (sl, Msg.type_unexpected e1)
        end
      end
      (* Subcase 2: Non-dependent type with placeholder *)
    | Lam(x, Meta n) ->
      begin match e1, e2 with 
      | Meta n1, Meta n2 ->
        begin match ty with
        | Type m -> Ok (Pathd(Lam(x, Meta n), Meta n1, Meta n2), Type m, sl)
        | Meta m -> Ok (Pathd(Lam(x, Meta n), Meta n1, Meta n2), Meta m, sl)
        | _ -> Error (sl, Msg.not_a_type ty)
        end
      | _ ->
        (* Neither endpoint is a placeholder *)
        let elab1 = elaborate global ind_env ctx lvl sl h1  vars e1 in
        let elab2 = elaborate global ind_env ctx lvl sl h1  vars e2 in
        begin match elab1, elab2 with
        | Ok (e1', tye1', sa1), Ok (e2', tye2', sa2) ->
          (* Target type is well-specified *)
          begin match ty, tye1', tye2' with
          | Type m, tye1, Meta _ -> Ok (Pathd(Lam(x, tye1), e1', e2'), Type m, Stack.append sa1 sa2)
          | Type m, Meta _, tye2 -> Ok (Pathd(Lam(x, tye2), e1', e2'), Type m, Stack.append sa1 sa2)
          | Type m, tye1, _ ->
            Ok (Pathd(Lam(x, tye1), e1', e2'), Type m, Stack.append sa1 sa2)
          (* If target type is also a placeholder we pick a well-specified type of an endpoint*)
          | Meta _, tye1, Meta _ ->
            let h2 = Placeholder.generate () in
            begin match elaborate global ind_env ctx lvl sl h2  vars tye1 with
            | Ok (tye1, tTye1, _) -> Ok (Pathd(Lam(x, tye1), e1', e2'), tTye1, Stack.append sa1 sa2)
            | Error (_, msg) -> Error (Stack.append sa1 sa2, Msg.not_a_type_2 tye1 msg)
            end  
          | Meta _, _, tye2 ->
            let h2 = Placeholder.generate () in
            begin match elaborate global ind_env ctx lvl sl h2  vars tye2 with
            | Ok (tye2, tTye2, _) -> Ok (Pathd(Lam(x, tye2), e1', e2'), tTye2, Stack.append sa1 sa2)
            | Error (_, msg) -> Error (Stack.append sa1 sa2, Msg.not_a_type_2 tye2 msg)
            end
          | _ -> 
            Error (Stack.append sa1 sa2, Msg.not_a_type ty)
            end
        | Ok _, Error (sa, msg) -> Error (sa, Msg.type_unexpected_2 e2 msg)
        | Error (sa, msg), _ -> 
          Error (sa, Msg.type_unexpected_3 e1 n msg)
        end
      end
    (* Now consider the case where the type line is well-specified *)
    | ty1 ->
      let elabi0 = elaborate global ind_env ctx lvl sl h1  vars (eval ind_env (App (ty1, I0()))) in
      let elabi1 = elaborate global ind_env ctx lvl sl h1  vars (eval ind_env (App (ty1, I1()))) in
      begin match elabi0, elabi1 with
      | Ok (tyi0, tTyi0, _), Ok (tyi1, _, _) ->
        let elab = elaborate global ind_env ctx lvl sl h1  vars (eval ind_env ty1) in
        let elab1 = elaborate global ind_env ctx lvl sl tyi0  vars (eval ind_env e1) in
        let elab2 = elaborate global ind_env ctx lvl sl tyi1  vars (eval ind_env e2) in
        begin match elab, elab1, elab2 with
        | Ok (ty1', Pi(_, i, ty2), sa), Ok (e1', _, sa1), Ok (e2', _, sa2) ->
          begin match eval ind_env i, eval ind_env ty2 with
          | Int(), Type n | Meta _, Type n ->
            begin match ty with
            | Type m ->
              if Level.leq n m then 
                Ok (Pathd(ty1', e1', e2'), Type m, Stack.lappend sa sa1 sa2) 
              else if Level.is_arbitrary m then 
                Ok (Pathd(ty1', e1', e2'), Type n, Stack.lappend sa sa1 sa2)
              else 
                Error (Stack.lappend sa sa1 sa2, Msg.pathd_ty ty1' e1' e2' ty)
            | Meta _ -> 
              Ok (Pathd(ty1', e1', e2'), Type n, Stack.lappend sa sa1 sa2)
            | _ -> Error (Stack.lappend sa sa1 sa2, Msg.not_a_type ty2)
            end
          | Int() , Meta _ | Meta _, Meta _ -> 
            Ok (Pathd(ty1', e1', e2'), tTyi0, Stack.lappend sa sa1 sa2)
          | _ -> 
            Error (Stack.lappend sa sa1 sa2, Msg.interval_unify i)
          end
        | Ok (ty1', _, sa), Ok _, Ok _ -> Error (sa, Msg.not_a_pi_type ty1')
        | Error (sa, msg), _, _| _, Error (sa, msg), _ | _, _, Error (sa, msg) -> 
          Error (sa, Msg.pathd_generic ty1 e1 e2 msg)
        end
      | Error (sa, msg), _ | _, Error (sa, msg) -> Error (sa, Msg.pathd_generic ty1 e1 e2 msg)
      end
    end
    
  | Type n ->
    begin match Level.is_declared lvl n with
    | Ok _ ->
      begin match ty with
      | Type m ->
        if Level.leq n m then 
          Ok (Type n, Type m, sl) 
        else if Level.is_arbitrary m then 
          Ok (Type n, Type m, sl)
        else
          Error (sl, Msg.universe_inconsitency n m)
      | Meta _ -> 
        Ok (Type n, Type (Suc n), sl)
      | _ -> Error (sl, Msg.type_mismatch n ty)
      end
    | Error msg -> 
      Error (sl, msg)
    end
  
  | Meta n ->
    Ok (Meta n, ty, sl)
    
  | Wild n ->
    let solved, used = sl in
    (* If the placeholder has already synthesized replace it *)
    begin match List.find_opt (fun (n', _, _) -> n = n') solved with
    | Some (_, e', _) -> Ok (Global e', ty, sl)
    | None ->
      begin match find n global ind_env ctx ty lvl sl  vars with (* false*)
      | Ok (e', ty') ->
        let sl' = ((n, e', ty') :: solved, used) in
        Ok (Global e', ty, sl')
      | Error _ -> Error (([], []), Msg.synthesis_error ind_env ty n ctx)
      end
    end

  | Subgoal () -> Error (sl, Msg.display_goal ctx ty)

(* Finds a variable in a context for a given type up to unification *)

and find n global ind_env ctx ty lvl sl  vars =
  let forbidden = snd sl in
  let rec search = function
    | [] -> Error "Can't find match"
    | (id, ty', _) :: ctx' ->
      if List.mem (n, id) forbidden then search ctx'
      else if ty' = ty then 
        Ok (id, ty) (* syntactic equality fast path *)
      else
        (* We ignore their types since they are assumed to be well-typed *)
        let h1 = Placeholder.generate () in
        match unify global ind_env ctx lvl sl  vars (ty, ty', h1) true with
        | Ok uty -> Ok (id, uty)
        | Error _ -> search ctx'
  in
  search ctx

(* Unifies two expressions at type *)

and unify global ind_env ctx lvl sl vars x lift =
  match x with
  | e, e', ty ->
    if e = e' then
      Ok e
    else
      match e, e', ty with
      | Meta n1, Meta n2, _ ->
        if n1 <= n2 then Ok (Meta n1) else Ok (Meta n2)
      
      | e , Meta n, Pathd(_, _, _) ->
        Hashtbl.add Data.meta_store n { Data.solution = e}; Ok e
      
      | e , _, Pathd(_, _, _) ->
        Ok e

      | e , Meta n, _ | Meta n, e, _ ->
        Hashtbl.add Data.meta_store n { Data.solution = e}; Ok e

      | Pi (_, ty1, ty2), Pi (_, ty1', ty2'), ty ->
        (* For now we just evaluate, soon we'll only evaluate if they are values *)
        let ty1 = eval ind_env ty1 in 
        let ty1' = eval ind_env ty1' in
        let u1 = unify global ind_env ctx lvl sl  vars (ty1, ty1', ty) lift in
        begin match u1 with
        | Ok s1 -> 
          let v1 = Expr.init_fresh vars in
          let ty2_open = Expr.fullsubst 0 ty1 s1 true (Expr.open_bound (Global v1) ty2) in
          let ty2'_open = Expr.fullsubst 0 ty1' s1 true (Expr.open_bound (Global v1) ty2') in
          let ty2_open = eval ind_env ty2_open in
          let ty2'_open = eval ind_env ty2'_open in
          let u2 = unify global ind_env ((v1, s1, true) :: ctx) lvl sl  (vars+1) (ty2_open, ty2'_open, ty) lift in
          begin match u2 with
          | Ok s2 -> Ok (Pi (v1, s1, Expr.close_bound v1 s2))
          | Error (sa, msg) -> Error (sa, Msg.unify_pi msg)
          end
        | Error ((e1, e2), msg) -> Error ((e1, e2), Msg.unify_pi msg)
        end

      | Pathd (e, e1, e2) , Pathd (e', e1', e2'), ty ->
        let e = eval ind_env e and e' = eval ind_env e' in
        let e1 = eval ind_env e1 and e1' = eval ind_env e1' in
        let e2 = eval ind_env e2 and e2' = eval ind_env e2' in
        let u = unify global ind_env ctx lvl sl  vars (e, e', Pi("v?", Int(), ty)) lift in
        let u1 = unify global ind_env ctx lvl sl  vars (e1, e1', eval ind_env (App(e, I0()))) lift in
        let u2 = unify global ind_env ctx lvl sl  vars (e2, e2', eval ind_env (App(e, I1()))) lift in
        begin match u, u1, u2 with
        | Ok s, Ok s1, Ok s2 -> Ok (Pathd (s, s1, s2))
        | Error (sa, msg), _, _ | _ , Error (sa, msg), _ | _, _ , Error (sa, msg) -> 
          Error (sa, Msg.unify_pathd e e1 e2 e' e1' e2' msg)
        end

      | Lam (x, e), Lam (x', e'), Pi(_, ty1 , ty2) ->
        if e = e' then
          Ok (Lam (x, e))
        else if Placeholder.is e' then
          (* Probably want to add to hashtbl *)
          Ok (Lam (x, e))
        else if Placeholder.is e then
          (* Here too *)
          Ok (Lam (x, e'))
        else 
          begin match eval ind_env ty1 with
          | Int() | Meta _ ->
            (* Local boundary separation *)
            let h1 = Placeholder.generate () in
            let elabt0 = elaborate global ind_env ctx lvl sl h1  vars (Expr.open_var 0 (I0()) ty2) in
            let elabt1 = elaborate global ind_env ctx lvl sl h1  vars (Expr.open_var 0 (I1()) ty2) in
            begin match elabt0, elabt1 with
            | Ok (tyi0, _, _), Ok (tyi1, _, _) ->
              let elab0 = elaborate global ind_env ctx lvl sl tyi0  vars (Expr.open_var 0 (I0()) e) in
              let elab0' = elaborate global ind_env ctx lvl sl tyi0  vars (Expr.open_var 0 (I0()) e') in
              let elab1 = elaborate global ind_env ctx lvl sl tyi1  vars (Expr.open_var 0 (I1()) e) in
              let elab1' = elaborate global ind_env ctx lvl sl tyi1  vars (Expr.open_var 0 (I1()) e') in
              begin match elab0, elab0', elab1, elab1' with
              | Ok (ei0, _, _), Ok (ei0', _, _), Ok (ei1, _, _), Ok (ei1', _, _) -> 
                let u0 = unify global ind_env ctx lvl sl  vars (ei0, ei0', tyi0) lift in
                let u1 = unify global ind_env ctx lvl sl  vars (ei1, ei1', tyi1) lift in
                begin match u0, u1 with
                | Ok _, Ok _ -> Ok (Lam (x, e))
                | Error msg, _ | _, Error msg -> Error msg
                end
              | Error (_, msg), _, _, _ | _, Error (_, msg), _, _ | _, _, Error (_, msg), _ | _, _, _, Error (_, msg) ->
                (* Fallback case (identical to what goes below) *)
                let v1 = Expr.init_fresh vars in
                let ev1 = Expr.open_var 0 (Global v1) e in
                let ev1' = Expr.open_var 0 (Global v1) e' in
                let tyv1 = Expr.open_var 0 (Global v1) ty2 in
                let u = unify global ind_env ((v1, ty1, true) :: ctx) lvl sl  (vars+1) (ev1, ev1', tyv1) lift in
                begin match u with
                | Ok s -> Ok (Lam (v1, s))
                | Error _ ->
                  Error ((Lam (x, e), Lam (x', e')), Msg.endpoint_unify e x e' x' msg)
                  end
              end
            | Error (_, msg), _ | _, Error (_, msg) -> (* This case is impossible *)
              Error ((Lam (x, e), Lam (x', e')), msg)
            end
          | _ ->
            let v1 = Expr.init_fresh vars in
            let ev1 = Expr.open_var 0 (Global v1) e in
            let ev1' = Expr.open_var 0 (Global v1) e' in
            let tyv1 = Expr.open_var 0 (Global v1) ty2 in
            let u = unify global ind_env ((v1, ty1, true) :: ctx) lvl sl  (vars+1) (ev1, ev1', tyv1) lift in
            begin match u with
            | Ok s -> Ok (Lam (v1, s))
            | Error msg -> Error msg
            end
          end
      
      (* Local boundary separation *)
      | e, e', Pi(_, Int() , ty) ->
        (* Determine i0-endpoints and type *)
        let ty0 = Expr.open_var 0 (I0()) ty in
        let e0 = eval ind_env (App (e, I0())) in
        let e0' = eval ind_env (App (e', I0())) in
        (* Determine i0-endpoints and type *)
        let ty1 = Expr.open_var 0 (I1()) ty in
        let e1 = eval ind_env (App (e, I1())) in
        let e1' = eval ind_env (App (e', I1())) in
        (* Elaboration for endpoint reduction *)
        let h1 = Placeholder.generate () in
        let elabt0 = elaborate global ind_env ctx lvl sl h1  vars ty0 in
        let elabt1 = elaborate global ind_env ctx lvl sl h1  vars ty1 in
            begin match elabt0, elabt1 with
            | Ok (ty0, _, _), Ok (ty1, _, _) ->
              let elab0 = elaborate global ind_env ctx lvl sl ty0  vars e0 in
              let elab0' = elaborate global ind_env ctx lvl sl ty0  vars e0' in
              let elab1 = elaborate global ind_env ctx lvl sl ty1  vars e1 in
              let elab1' = elaborate global ind_env ctx lvl sl ty1  vars e1' in
              begin match elab0, elab0', elab1, elab1' with
              | Ok (e0, _, _), Ok (e0', _, _), Ok (e1, _, _), Ok (e1', _, _) -> 
                let u0 = unify global ind_env ctx lvl sl  vars (e0, e0', ty0) lift in
                let u1 = unify global ind_env ctx lvl sl  vars (e1, e1', ty1) lift in
                begin match u0, u1 with
                | Ok _, Ok _ -> Ok e
                | Error (_, msg), _ -> 
                  Error ((e0, e0'), Msg.app_unify_i0 ind_env e0 e0' msg)
                | _, Error (_, msg) -> Error ((e1, e1'), Msg.app_unify_i1 e1 e1' msg)
                end
              | Error (_, msg), _, _, _ | _, Error (_, msg), _, _ | _, _, Error (_, msg), _ | _, _, _, Error (_, msg) -> 
                Error ((e, e'), Msg.endpoint_unify_generic msg)
              end
            | Error (_, msg), _ | _, Error (_, msg) -> (* This case is impossible *)
              Error ((e, e'), Msg.endpoint_unify_generic msg)
            end

      | App (e1, e2), App (e1', e2'), ty ->
        let h1 = Placeholder.generate () in
        let elab2 = elaborate global ind_env ctx lvl sl h1  vars e2 in
        begin match elab2 with
        | Ok (_, ty2, _) ->
          let u2 = unify global ind_env ctx lvl sl  vars (e2, e2', ty2) lift in
          let v1 = Expr.init_fresh vars in
          let u1 = unify global ind_env ctx lvl sl  (vars+1) (e1, e1', Pi(v1, ty2, Expr.fullsubst 0 e2 (Local 0) true ty)) lift in
          begin match u1, u2 with
          | Ok s1, Ok s2 -> Ok (App (s1, s2))
          | Error (ex, msg), _ | _, Error (ex, msg) ->
            (* Check for metavariable application *)
            let head, args = Eval.break_args [] (App (e1, e2)) in
            begin match solve_meta_application args vars (App(e1', e2')) head with
            | Some s -> Ok s
            | None ->
              let head, args = Eval.break_args [] (App (e1', e2')) in
              begin match solve_meta_application args vars (App(e1, e2)) head with
              | Some s -> Ok s
              | None ->

            (* If not unifiable check endpoints *)            
            let helper x y = 
              match x, y with
              | Ok _, Ok _ -> Ok (App (e1, e2))
              | Error (ex, msg), _ | _, Error (ex, msg) -> 
                Error (ex, msg)
            in
            begin match eval ind_env e2, eval ind_env e2', eval ind_env ty2 with
            | Global _, Global _, Int() ->
              let i0 x = eval ind_env (App (x, I0())) in
              let i1 x = eval ind_env (App (x, I1())) in
              let ui0 = unify global ind_env ctx lvl sl  (vars+1) (i0 e1, i0 e1', ty2) lift in
              let ui1 = unify global ind_env ctx lvl sl  (vars+1) (i1 e1, i1 e1', ty2) lift in
              helper ui0 ui1
            
            | _, Global _, Int() ->
              let i0 x = eval ind_env (App (x, I0())) in
              let i1 x = eval ind_env (App (x, I1())) in
              let ui0 = unify global ind_env ctx lvl sl  (vars+1) (App (e1, e2), i0 e1', ty2) lift in
              let ui1 = unify global ind_env ctx lvl sl  (vars+1) (App (e1, e2), i1 e1', ty2) lift in
              helper ui0 ui1
            
            | Global _, _, Int() ->
              let i0 x = eval ind_env (App (x, I0())) in
              let i1 x = eval ind_env (App (x, I1())) in
              let ui0 = unify global ind_env ctx lvl sl  (vars+1) (i0 e1, App (e1', e2'), ty2) lift in
              let ui1 = unify global ind_env ctx lvl sl  (vars+1) (i1 e1, App (e1', e2'), ty2) lift in
              helper ui0 ui1

            | _ ->
              (* Try again now by evaluating both applications *)
              let app1 = App (e1, e2) in
              let app2 = App (e1', e2') in
              (* TODO: this is not ideal, to avoid re-evaluation, better store values in a hasthtable and look them up *)
              let app1' = eval ind_env app1 in
              let app2' = eval ind_env app2 in
              if app1 = app1' && app2 = app2' then
                Error (ex, Msg.app_unify_fallback e1 e2 e1' e2' msg)
              else
                unify global ind_env ctx lvl sl  (vars+1) (app1', app2', ty) lift
            end
          end
          end
          end
        | Error (_, msg) -> (* This case is impossible *)
          Error ((App (e1, e2), App (e1', e2')), Msg.app_unify_arg e2 h1 msg)
        end
      
      | App (e, i), e', _ | e', App (e, i), _ ->
        (* Try endpoint unification *)
          let h1 = Placeholder.generate () in
          let elab2 = elaborate global ind_env ctx lvl sl h1  vars i in
          begin match elab2, i with
          | Ok (_, Int(), _), Global _ ->
            let e0 = eval ind_env (App (e, I0())) in
            let e1 = eval ind_env (App (e, I1())) in
            let e0' = eval ind_env (Expr.fullsubst 0 i (I0()) true e') in
            let e1' = eval ind_env (Expr.fullsubst 0 i (I1()) true e') in
            let ui0 = unify global ind_env ctx lvl sl  vars (e0, e0', ty) lift in
            let ui1 = unify global ind_env ctx lvl sl  vars (e1, e1', ty) lift in
            begin match ui0, ui1 with
            | Ok _, Ok _ -> Ok (App (e, i))
            | Error (_, msg), _ -> Error ((e0, e0'), Msg.app_unify_i0 ind_env e0 e0' msg)
            | _, Error (_, msg) -> Error ((e1, e1'), Msg.app_unify_i1 e1 e1' msg)
            end
          | _ ->
            (* Needs more testing to confirm soundness *)
            begin match e with
            | Meta _ -> (* we take Meta to be (\lambda x. e') *)
              Ok e'
            | _ -> Error ((e, e'), Msg.app_unify_app e i e')
            end
            (* Fallback case: try again after evaluating the second argument *)
            (* let i = eval ind_env i in
            let app = eval ind_env (App (e, i)) in
            if app = App(e, i) then (* TODO: optimize reevaluation with hash consing *)
              Error ((e, e'), "Don't know how to unify the applied term\n  " ^ Pretty.printf (App (e, i)) ^ "\nwith\n  " ^ Pretty.printf e')
            else
              unify global ind_env ctx lvl sl  vars (app, e', ty) lift *)
          end
      
      | Coe (i, j, e1, e2) , Coe (i', j', e1', e2'), _ ->
        let ui = unify global ind_env ctx lvl sl  vars (i, i', Int()) lift in
        let uj = unify global ind_env ctx lvl sl  vars (j, j', Int()) lift in
        let h0 = Placeholder.generate () in
        let elab = elaborate global ind_env ctx lvl sl h0  vars e1 in
        begin match elab with
        | Ok (_, eTy, _) ->
          let u1 = unify global ind_env ctx lvl sl  vars (e1, e1', eTy) lift in
          let e2 = eval ind_env e2 and e2' = eval ind_env e2' in
          let u2 = unify global ind_env ctx lvl sl  vars (e2, e2', eval ind_env (App(e1', i'))) lift in
          begin match ui, uj, u1, u2 with
          | Ok si, Ok sj, Ok s1, Ok s2 -> Ok (Coe (si, sj, s1, s2))
          | Error msg, _, _, _ | _ , Error msg, _, _ | _ , _, Error msg, _ | _ , _, _, Error msg -> 
            Error msg
          end
        | Error (_, msg) -> 
          Error ((Coe (i, j, e1, e2) , Coe (i', j', e1', e2')), msg)
        end
      
      | Hcom (i, j, e, e1, e2) , Hcom (i', j', e', e1', e2'), _ ->
        let h0 = Placeholder.generate () in
        let elab = elaborate global ind_env ctx lvl sl h0  vars e in
        (* Syntactic equality as interval variables are expected to be atoms *)
        (* NOTE: better to ensure safety by replacing expr types with atom *)
        if i = i' && j = j' then
          begin match elab with
          | Ok (_, eTy, _) ->
            let u = unify global ind_env ctx lvl sl  vars (e, e', eTy) lift in
            let u1 = unify global ind_env ctx lvl sl  vars (e1, e1', eTy) lift in
            let u2 = unify global ind_env ctx lvl sl  vars (e2, e2', eTy) lift in
            begin match u, u1, u2 with
            | Ok se, Ok se1, Ok se2 -> Ok (Hcom (i, j, se, se1, se2))
            | Error msg, _, _ | _ , Error msg, _ | _ , _, Error msg -> 
              Error msg
            end
          | Error (_, msg) -> 
            Error ((Hcom (i, j, e, e1, e2) , Hcom (i', j', e', e1', e2')), msg)
          end
        else
          Error ((Hcom (i, j, e, e1, e2) , Hcom (i', j', e', e1', e2')), Msg.hcom_unify i i' j j')

      | At (Meta _, Meta _), e', _ | e', At (Meta _, Meta _), _ ->
        Ok e'
      
      | At (e1, e2), At (e1', e2'), ty ->
        let u2 = unify global ind_env ctx lvl sl  vars (e2, e2', Int()) lift in
        let h1 = Placeholder.generate () in
        let h2 = Placeholder.generate () in
        let v1 = Expr.init_fresh vars in
        let elab1 = elaborate global ind_env ctx lvl sl (Pathd (Pi(v1, Int(), Expr.fullsubst 0 e2 (Local 0) true ty), h1, h2))  (vars+1) e1 in
        begin match elab1 with
        | Ok (_, ety, _) ->
          let u1 = unify global ind_env ctx lvl sl  (vars+1) (e1, e1', ety) lift in
          begin match u1, u2 with
          | Ok s1, Ok s2 -> Ok (At (s1, s2))
          | Error msg, _ | _, Error msg -> Error msg
          end
        | Error (_, msg) ->
          Error ((At (e1, e2), At (e1', e2')), msg)
        end

      | At (e, i), e', ty | e', At (e, i), ty ->

        (* If i = ε we elaborate and unify e @ ε with e' : ty *)
        if i = I0() || i = I1() then
          let elab = elaborate global ind_env ctx lvl sl ty  vars (At (e, i)) in
          begin match elab with
          | Ok (ei, ety, _) ->
            let u1 = unify global ind_env ctx lvl sl  vars (ei, e', ety) lift in
            begin match u1 with
            | Ok se -> Ok se
            | Error msg -> Error msg
            end
          | Error (_, msg) ->
            Error ((At (e, i), e'), msg)
          end
        
        (* Otherwise elaborate and unify e @ ε with e' [ε/i] : ty [ε/i] *)
        else
          let h1 = Placeholder.generate () in
          begin match i with
          | Global x ->
            (* Infer the endpoints of the type line *)
            let elabt0 = elaborate global ind_env ctx lvl sl h1  vars (eval ind_env (Global.subst_global 0 (I0()) x ty)) in
            let elabt1 = elaborate global ind_env ctx lvl sl h1  vars (eval ind_env (Global.subst_global 0 (I1()) x ty)) in
            begin match elabt0, elabt1 with
            | Ok (ty0, _, _), Ok (ty1, _, _) ->
              (* Check that the endpoints of e inhabit the type line endpoints *)
              let elab0 = elaborate global ind_env ctx lvl sl ty0  vars (At (eval ind_env (Global.subst_global 0 (I0()) x e), I0())) in
              let elab1 = elaborate global ind_env ctx lvl sl ty1  vars (At (eval ind_env (Global.subst_global 0 (I1()) x e), I1())) in
              (* Check that the endpoints of e' inhabit the type line endpoints *)
              let elab0' = elaborate global ind_env ctx lvl sl ty0  vars (eval ind_env (Global.subst_global 0 (I0()) x e')) in
              let elab1' = elaborate global ind_env ctx lvl sl ty1  vars (eval ind_env (Global.subst_global 0 (I1()) x e')) in
              begin match elab0, elab1, elab0', elab1' with
              | Ok (e0, _, _), Ok (e1, _, _), Ok (e0', _, _), Ok (e1', _, _) ->
                (* Unify the corresponding endpoints of e and e' *)
                let ui0 = unify global ind_env ctx lvl sl  vars (e0, e0', ty0) lift in
                let ui1 = unify global ind_env ctx lvl sl  vars (e1, e1', ty1) lift in
                begin match ui0, ui1 with
                | Ok _, Ok _ -> Ok (App (e, i))
                | Error (_, msg), _ -> Error ((e0, e0'), Msg.generic_unify e0 e0' msg) 
                | _, Error (_, msg) -> Error ((e1, e1'), Msg.generic_unify e1 e1' msg)
                end
              | Error (_, msg), _, _, _ | _, Error (_, msg), _, _ | _, _, Error (_, msg), _ |  _, _, _, Error (_, msg) ->
                Error ((At (e, i), e'), msg)
              end

            | Error (_, msg), _ | _, Error (_, msg) -> 
              Error ((At (e, i), e'), msg) (* This case is impossible *)
            end
          | _ ->
            Error ((e, e'), Msg.generic_unify_2 (App (e, i)) e')
          end

      | Abort e, Abort e', _ ->
        let u = unify global ind_env ctx lvl sl  vars (e, e', Void()) lift in
        begin match u with
        | Ok s -> Ok (Abort s)
        | Error msg -> Error msg
        end

      | Type m, Type n, _ ->
        (* Helper compare function *)
        let compare m n = if lift then if Level.leq n m then Ok (Type n) else
            Error ((Type m, Type n), Msg.universe_unify m n)
          else
            Error ((Type m, Type n), Msg.universe_unify_2 m n)
        in
        begin match m, n with
        | Var par, _ when Level.is_arbitrary_string par -> Ok (Type n)
        | _, Var par when Level.is_arbitrary_string par -> Ok (Type m)
        | m, n -> compare m n
        end
      
      | Lam (x, e) , e', _ | e', Lam (x, e), _ ->
        let e1 = eval ind_env e in
        let abs = eval ind_env (Lam (x, e1)) in (* for any possible eta reduction *)
        (* Needs to be optimized to avoid reevaluation *)
        if Lam (x, e) = abs && not (e' = abs) then
          Error ((Lam (x, e), e'), Msg.lam_unify x e e')
        else
          unify global ind_env ctx lvl sl  vars (abs, e', ty) lift
      
      | Pabs (i, e) , e', _ | e', Pabs (i, e), _ ->
        let e1 = eval ind_env e in
        let pabs = eval ind_env (Pabs (i, e1)) in (* for any possible eta reduction *)
        (* Needs to be optimized to avoid reevaluation *)
        if Pabs (i, e) = pabs && not (e' = pabs) then
          Error ((Pabs (i, e), e'), Msg.pabs_unify i e e')
        else
          unify global ind_env ctx lvl sl  vars (pabs, e', ty) lift

      | e , e', _ -> 
        if eval ind_env e = eval ind_env e' then 
          Ok e 
        else 
          Error ((e, e'), Msg.not_syntactically_equal e e')