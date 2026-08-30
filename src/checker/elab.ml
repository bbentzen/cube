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

(* TODO: Retool vars as a list of used globals *)

let goal_msg ctx e ty =
  "when checking that\n  " ^ Pretty.printf e ^ "\nhas the expected type\n" ^ Global.printf ctx ^ 
  "-------------------------------------------\n ⊢ " ^ Pretty.printf ty

(* Checks whether the type of a given expression is the given type *)

let rec elaborate global ind_env ctx lvl sl ty ph vars = function
  | Global x ->
    begin match Global.var_type x ctx with
    | Ok xty ->
      (* let ty = eval ind_env ty in *)
      let c = Global.check_var_ty x ty ctx in
      let h = Placeholder.is ty in 
      let h' = Placeholder.is xty in 
      let d = Global.is_declared x ctx in
      begin match c, h, h', d with
      | true , _, _ , _ | _ , _, true , _ ->  
        Ok (Global x, ty, sl)
      | _ , true, _ , _ ->  
        Ok (Global x, xty, sl)
      | false , false, false , true ->
        let h1 = Placeholder.generate ph [] in
        begin match elaborate global ind_env ctx lvl sl h1 (ph+1) vars xty with
        | Ok (_, tTy', sa) ->
          let u = unify global ind_env ctx lvl sl (ph+1) vars (eval ind_env ty, eval ind_env xty, tTy') true in
          begin match u with
          | Ok s -> 
            Ok (Global x, s, sl) 
          | Error (_, msg) ->
              Error (sa, "The variable " ^ x ^ " has type\n   " ^ Pretty.printf xty ^ 
                  "\nbut is expected to have type\n  " ^ Pretty.printf ty ^ "\n" ^ msg)
          end
        | Error (sa, msg) -> (* This case is impossible *)
          Error (sa, "Error at type checking the variable " ^ x ^ ": " ^ msg)
        end
      | false , false, false , false -> 
        begin match Env.unfold x global with
        | Ok (_, xty) ->
          let h1 = Placeholder.generate ph [] in
          begin match elaborate global ind_env ctx lvl sl h1 (ph+1) vars xty with
          | Ok (_, tTy', sa) ->
            let u = unify global ind_env ctx lvl sl (ph+1) vars (eval ind_env xty, eval ind_env ty, tTy') true in
            begin match u with
            | Ok s -> Ok (Global x, s, sl) (* runs faster when not body *)
            | _ -> 
              Error (sa, x ^ " has type \n  " ^ Pretty.printf xty ^ "\nbut is expected to have type\n  " ^ Pretty.printf ty)
            end
          | Error (sa, msg) -> (* This case is impossible *)
            Error (sa, "Error with global variables: " ^ msg)
          end
        | Error msg -> 
          Error (sl, "Error with global variables: " ^ msg)
        end
      end
    | Error _ -> 
      Error (sl, "No declaration for the variable " ^ x)
    end
    
  | I0() ->
    begin match ty with
    | Int() -> 
      Ok (I0(), Int(), sl)
    | Hole _ -> 
      Ok (I0(), Int(), sl)
    | _ -> Error (sl, "Type mismatch when checking that the endpoint i0 of type I has type " ^ Pretty.printf ty)
  end
  
  | I1() ->
    begin match ty with
    | Int() -> 
      Ok (I1(), Int(), sl)
    | Hole _ -> 
      Ok (I1(), Int(), sl)
    | _ -> Error (sl, "Type mismatch when checking that the endpoint i1 of type I has type " ^ Pretty.printf ty)
    end

  | Lam (x, e) ->
    let e = eval ind_env e in
    let ty = eval ind_env ty in
    begin match ty with
    | Pi (_, ty1, ty2) ->
      let v1 = Expr.init_fresh vars in
      let e' = Expr.open_var 0 (Global v1) e in
      let ty2' = Expr.open_var 0 (Global v1) ty2 in
      let elab = elaborate global ind_env ((v1, ty1, true) :: ctx) lvl sl ty2' ph (vars+1) e' in
      begin match elab with
      | Ok (e', ty2', sa) -> 
        Ok (Lam (x, Expr.close_bound v1 e'), Pi (x, ty1, Expr.close_bound v1 ty2'), sa)
      | Error (sa, msg) -> Error (sa, msg)
      end
    | Hole _ ->
      let h1 = Placeholder.generate ph [] in
      let h2 = Placeholder.generate (ph+1) [] in
      elaborate global ind_env ctx lvl sl (Pi(x, h1, h2)) (ph+2) vars (Lam (x, e))
    | _ -> 
      Error (sl, "The term\n  " ^ Pretty.printf (Lam (x, e)) ^ 
      "\nhas type\n  " ^ Pretty.printf ty ^ "\nbut is expected to have type\n  Π (v? : ?0?) ?1?")
    end

  | App (e1, e2) ->
    (* If the head expression is a recursor try to infer the motive *)
    let ty = eval ind_env ty in
    let head, args = Eval.break_args [] (App (e1, e2)) in
    let rec_env, cons_env = ind_env in 
    begin match Infer.try_infer_motive rec_env ty args head with
    | Some res ->
      elaborate global ind_env ctx lvl sl ty ph vars res
    | None ->
      (* If the head expression is a constructor try to infer indices *)
      begin match Infer.constr_indices cons_env ty args head with
      | Some res ->
        elaborate global ind_env ctx lvl sl ty ph vars res
      | None ->
        (* Otherwise infer the type of e1 and check its evaluated domain against e2 *)
        let h1 = Placeholder.generate ph [] in
        let v1 = Expr.init_fresh vars in
        let h2 = Placeholder.generate (ph+1) [] in
        let elab1 = elaborate global ind_env ctx lvl sl (Pi(v1, h1, h2)) (ph+2) (vars+1) e1 in
        begin match elab1 with
        | Ok (e1', Pi(_, ty1, ty2), sa1) ->
          (* Evaluates the inferred domain before type checking *)
          let ty1' = eval ind_env ty1 in
          let h3 = Placeholder.generate (ph+3) [] in
          let elab2 = elaborate global ind_env ctx lvl sl ty1' (ph+2) (vars+1) e2 in
          begin match elab2 with
          | Ok (e2', _, sa2) ->
            (* Otherwise unify both types possibly lifting the universe levels *)
            let ty2' = eval ind_env (Expr.open_var 0 e2' ty2) in
            let u = unify global ind_env ctx lvl sl (ph+3) (vars+1) (ty, ty2', h3) true in
            begin match u with
            | Ok _ -> 
              Ok (App (e1', e2'), ty2', Stack.append sa1 sa2)
            | Error (_, msg) ->
              Error (Stack.append sa1 sa2,
                "Failed application: the term in the argument position \n  " ^ Pretty.printf e2' ^ 
                "\nis expected to have type\n  " ^ Pretty.printf ty1' ^ "\n" ^ msg)
            end
          | Error (sa2, msg) -> 
            Error (Stack.append sa1 sa2,
              "Failed application: the term in the argument\n  " ^ Pretty.printf e2 ^ 
              "\nis expected to have type\n  " ^ Pretty.printf ty1' ^ "\n" ^ msg)
          end
          
        | Ok (e1', ty1', sa1) -> 
          Error (sa1,
            "Failed application: the term in function position\n  " ^ Pretty.printf e1' ^ 
            "\nis expected to have the type\n " ^ Pretty.printf h2 ^
            "\nbut was found to have type\n " ^ Pretty.printf ty1'
            )
        | Error (sa, msg) -> 
          Error (sa, 
          "Failed application: the term in function position\n  " ^ Pretty.printf e1 ^ 
            "\nis expected to have a function type.\n " ^ msg)
        end
      end
    end
    
  | Pair (e1, e2) -> 
    let e1 = eval ind_env e1 and e2 = eval ind_env e2 in
    let ty = eval ind_env ty in
    begin match ty with
    | Sigma(y, ty1, ty2) ->
      let elab1 = elaborate global ind_env ctx lvl sl ty1 ph vars e1 in
      let elab2 = elaborate global ind_env ctx lvl sl (Expr.open_var 0 e1 ty2) ph vars e2 in
      begin match elab1, elab2 with
      | Ok (e1', ty1', sa1), Ok (e2', ty2', sa2) ->
        begin match ty2 with
        | Hole (n, l) ->
          let ty' = Expr.fullsubst 0 e1' (Hole (n, e1 :: e1' :: Global y :: l)) true ty2' in
          Ok (Pair (e1', e2'), Sigma(y, ty1', ty'), Stack.append sa2 sa1)
        | _ ->
          let ty' = Expr.fullsubst 0 e1' (Global y) true ty2' in (* to be improved *)
          Ok (Pair (e1', e2'), Sigma(y, ty1', ty'), Stack.append sa2 sa1)
        end
      | Error msg, _ | _, Error msg -> 
        Error msg
      end
    | Hole _ -> 
      let v1 = Expr.init_fresh vars in
      let h1 = Placeholder.generate ph [] in
      let h2 = Placeholder.generate (ph+1) [] in
      elaborate global ind_env ctx lvl sl (Sigma(v1, h1, h2)) (ph+2) (vars+1) (Pair (e1, e2))
    | _ ->
      Error (sl, "Type mismatch when checking that the term (" ^ 
      Pretty.printf e1 ^ ", " ^ Pretty.printf e2 ^ ") of type Σ (v? : ?0?) ?1? has type " ^ Pretty.printf ty)
    end
    
  | Fst e ->
    let h1 = Placeholder.generate ph [] in
    let elab = elaborate global ind_env ctx lvl sl h1 (ph+1) vars e in
    begin match elab with
    | Ok (e', ty', sa) ->
      let ty' = eval ind_env ty' in
      begin match ty' with
      | Sigma(_, ty', _) -> 
        let elabTy = elaborate global ind_env ctx lvl sl h1 (ph+1) vars ty in
        begin match elabTy with
        | Ok (_, tTy, _) ->
          let u = unify global ind_env ctx lvl sl (ph+1) vars (eval ind_env ty, ty', tTy) false in
          begin match u with
          | Ok _ ->
            Ok (Fst e', ty', sa) 
          | Error (_, msg) ->
            Error (sa, "The term\n  " ^ Pretty.printf e' ^ "\nhas type \n  " ^ Pretty.printf ty' ^ "\nbut failed to unify it with the expected type\n  " ^ Pretty.printf ty ^ "\n" ^ msg)
          end
        | Error msg -> (* This case is impossible *)
          Error msg
        end
      | _ -> 
        Error (sa, "The term\n  " ^ Pretty.printf e' ^ "\nhas type\n  " ^ Pretty.printf ty' ^ "\nbut is expected to have type\n  Σ (v0 : ?0?) ?1?")
      end
    | Error (sa, msg) ->
      Error (sa, "The term\n  " ^ Pretty.printf e ^ "\nis expected to have type\n  Σ (v0 : ?0?) ?1?" ^ "\n" ^ msg)
    end

  | Snd e ->
    let h1 = Placeholder.generate ph [] in
    let elab = elaborate global ind_env ctx lvl sl h1 (ph+1) vars e in
    begin match elab with
    | Ok (e', ty', sa) ->
      let ty' = eval ind_env ty' in
      begin match ty' with
      | Sigma(_, _, ty2) ->
        let ty2' = Expr.open_var 0 (Fst e') ty2 in
        let elabTy = elaborate global ind_env ctx lvl sl h1 (ph+1) vars ty in
        begin match elabTy with
        | Ok (_, tTy, _) ->
          let u = unify global ind_env ctx lvl sl (ph+1) vars (eval ind_env ty, eval ind_env ty2', tTy) false in
          begin match u with
          | Ok _ ->
            Ok (Snd e', ty2', sa)
          | Error (_, msg) ->
            Error (sa, "The term\n  " ^ Pretty.printf e' ^ "\nhas type \n  " ^ Pretty.printf ty2' ^ "\nbut failed to unify it with the expected type\n  " ^ Pretty.printf ty ^ "\n" ^ msg)
          end
        | Error msg -> (* This case is impossible *)
          Error msg
        end
      | _ -> 
        Error (sa, "The projected term\n  " ^ Pretty.printf e' ^ "\nhas type\n  " ^ Pretty.printf ty' ^ "\nbut is expected to have type\n  Σ (v0 : ?0?) ?1?")
    end
    | Error (sa, msg) ->
      Error (sa, "The projected term\n  " ^ Pretty.printf e ^ "\nis expected to have type\n  Σ (v0 : ?0?) ?1?" ^ "\n" ^ msg)
    end

  | Abort e ->
    let elab = elaborate global ind_env ctx lvl sl (Void()) ph vars e in
    begin match elab with
    | Ok (e', _, sa) -> Ok (Abort e', ty, sa)
    | Error msg -> Error msg
    end
  
  | Coe(i, j, ety, e) ->
    let h0 = Placeholder.generate ph [] in
    let elabi = elaborate global ind_env ctx lvl sl (Int()) (ph+1) vars i in
    let elabj = elaborate global ind_env ctx lvl sl (Int()) (ph+1) vars j in
    let tyi_expr = eval ind_env (App(ety, i)) in
    let tyj_expr = eval ind_env (App(ety, j)) in
    let elabti = elaborate global ind_env ctx lvl sl h0 (ph+1) vars tyi_expr in
    let elabtj = elaborate global ind_env ctx lvl sl h0 (ph+1) vars tyj_expr in
    begin match elabi, elabj, elabti, elabtj with
    | Ok (i', _, _), Ok (j', _, _), Ok (tyi, eTy, sat), Ok (tyj, _, _) ->
      let e' = eval ind_env e in
      let elab = elaborate global ind_env ctx lvl sl (eval ind_env tyi) (ph+1) vars e' in
      let elabt = elaborate global ind_env ctx lvl sl h0 (ph+1) vars ty in
      begin match elab, elabt with
      | Ok (e', _, sa), Ok (ty', _, sat') ->
        let u = unify global ind_env ctx lvl sl (ph+1) vars (eval ind_env tyj, eval ind_env ty', eTy) false in
        begin match u with
        | Ok tty ->
          Ok (Coe (i', j', eval ind_env ety, e'), tty, Stack.lappend sa sat sat')
        | Error (_, msg) -> 
          Error (Stack.lappend sa sat sat', 
            "Failed to unify the terms\n  " ^ Pretty.printf tyj ^ "\nand\n  " ^ Pretty.printf ty' ^ 
            "\nof expected type\n  " ^ Pretty.printf eTy ^
            "\nwhen checking that the coercion\n  " ^ Pretty.printf (Coe(i, j, ety, e)) ^
            "\nhas type\n  " ^ Pretty.printf ty ^
            "\n" ^ msg)
        end
      | Error (sa, msg), _ ->
        Error (sa,
          "The coercion failed because\n  " ^ Pretty.printf e ^
          "\ndoes not have type\n  " ^ Pretty.printf tyi ^ "\n" ^ msg)
      | _, Error msg ->
        Error msg
      end
    | Error msg, _, _, _ ->
      Error msg
    | _, Error msg, _, _ ->
      Error msg
    | _, _, Error (sa, msg), _ ->
      Error (sa,
        "Failed while elaborating coercion family instance " ^ Pretty.printf tyi_expr ^ " at " ^ Pretty.printf i ^ "\n" ^ msg)
    | _, _, _, Error (sa, msg) ->
      Error (sa,
        "Failed while elaborating coercion family instance " ^ Pretty.printf tyj_expr ^ " at " ^ Pretty.printf j ^ "\n" ^ msg)
    end
  
  | Local index ->
    Error (sl,
      "Unexpected local variable when checking that the term " ^
      Pretty.printf (Local index) ^
      " has type " ^ Pretty.printf ty ^
      "\n" ^ Global.printf ctx)

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
        let elab = elaborate global ind_env ctx lvl sl jty ph vars e in
        let elab1 = elaborate global ind_env ctx lvl sl jty0 ph vars e1 in  (* subst i0 *)
        let elab2 = elaborate global ind_env ctx lvl sl jty1 ph vars e2 in  (* subst i1 *)
        begin match elab, elab1, elab2 with
        | Ok (e', ety, sa), Ok (e1', e1ty, sa1), Ok (e2', e2ty, sa2) ->
          (* Typecheck the endpoints of the lid *)
          let elabi0 = elaborate global ind_env ctx lvl sl ty0 ph vars (eval ind_env (App(e', I0()))) in
          let elabi1 = elaborate global ind_env ctx lvl sl ty1 ph vars (eval ind_env (App(e', I1()))) in
          (* Typecheck the i face of the tubes *)
          let elab1i0 = elaborate global ind_env ctx lvl sl ty0 ph vars (eval ind_env (App(e1', i1))) in
          let elab2i0 = elaborate global ind_env ctx lvl sl ty1 ph vars (eval ind_env (App(e2', i1))) in
          begin match elabi0, elabi1, elab1i0, elab2i0 with
          | Ok (ei0, _, _), Ok (ei1, _, _), Ok (e1i0, _, _), Ok (e2i0, _, _) ->
            (* Validate the composition scenario by matching the i-corners of the square *)
            let u1 = unify global ind_env ctx lvl sl ph vars (eval ind_env ei0, e1i0, ty0) false in
            let u2 = unify global ind_env ctx lvl sl ph vars (eval ind_env ei1, e2i0, ty1) false in
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
            | Error (_, msg), _ ->
              Error (Stack.lappend sa sa1 sa2,
                "Invalid composition scenario: Error when unifying the i0-endpoint of the lid \n  " ^ 
                Pretty.printf (eval ind_env ei0) ^ "\nwith the " ^ Pretty.printf i1 ^ "-endpoint of the i0-tube \n  " ^ Pretty.printf (eval ind_env e1i0) ^
                "\n" ^ msg)
            | _, Error (_, msg) -> 
              Error (Stack.lappend sa sa1 sa2, 
                "Invalid composition scenario: Error when unifying the terms\n  " ^ 
                Pretty.printf (eval ind_env ei1) ^ "\nwith the " ^ Pretty.printf i1 ^ "-endpoint of the i1-tube \n  " ^ Pretty.printf (eval ind_env e2i0) ^
                "\n" ^ msg)
            end
            
          | Error (sa', msg), _, _, _ ->
            Error (Stack.append sa' (Stack.lappend sa sa1 sa2), 
            "Error when checking that the homogeneous composition  " ^ Pretty.printf (Hcom(i1, j1, e', e1', e2')) ^ 
            "\nhas type\n  I → " ^ Pretty.printf ty' ^ 
            "\nThe i0-face of the lid\n  " ^ Pretty.printf (eval ind_env (App(e', I0()))) ^ "\ndoes not have the expected type\n  " ^ Pretty.printf ty' ^
            "\n" ^ msg)
          | _, Error (sa', msg), _, _ ->
            Error (Stack.append sa' (Stack.lappend sa sa1 sa2), 
            "Error when checking that the homogeneous filling\n  " ^ Pretty.printf (Hcom(i1, j1, e', e1', e2')) ^ 
            "\nhas type\n  I → I → " ^ Pretty.printf ty' ^ 
            "\nThe i1-face of the lid\n  " ^ Pretty.printf (eval ind_env (App(e', I1()))) ^ "\ndoes not have the expected type\n  " ^ Pretty.printf ty' ^ 
            "\n" ^ msg)
          | _, _, Error (sa', msg), _ ->
            Error (Stack.append sa' (Stack.lappend sa sa1 sa2), 
            "Error when checking that the homogeneous filling\n  " ^ Pretty.printf (Hcom(i1, j1, e', e1', e2')) ^ 
            "\nhas type\n  I → I → " ^ Pretty.printf ty' ^ 
            "\nThe i0-face of the i0-tube\n  " ^ Pretty.printf (eval ind_env (App(e1', I0()))) ^ "\ndoes not have the expected type\n  " ^ Pretty.printf ty' ^ 
            "\n" ^ msg)
          | _, _, _, Error (sa', msg) ->
            Error (Stack.append sa' (Stack.lappend sa sa1 sa2), 
            "Error when checking that the homogeneous filling\n  " ^ Pretty.printf (Hcom(i1, j1, e, e1, e2)) ^ 
            "\nhas type\n  I → I → " ^ Pretty.printf ty' ^ 
            "\nThe i0-face of the i1-tube\n  " ^ Pretty.printf (eval ind_env (App(e2', I0()))) ^ "\ndoes not have the expected type\n  " ^ Pretty.printf ty' ^ 
            "\n" ^ msg)
          end
        | Error (sa, msg), _, _ | _, Error (sa, msg), _ | _, _, Error (sa, msg) -> 
          Error (sa, "Failed to typecheck the lid or tubes of the homogeneous composition: " ^ msg)
        end
      
      | Hole (_, _), Hole (_, _) -> 
        (* Infer the type of the lid and the tubes *)
        let h0 = Placeholder.generate ph [] in
        let elab = elaborate global ind_env ctx lvl sl (Pi("v1", Int(), h0)) (ph+1) vars e in
        let elab1 = elaborate global ind_env ctx lvl sl (Pi("v1", Int(), h0)) (ph+1) vars e1 in
        let elab2 = elaborate global ind_env ctx lvl sl (Pi("v1", Int(), h0)) (ph+1) vars e2 in
        begin match elab, elab1, elab2 with
        | Ok (e', ety, ss), Ok (e1', _, _), Ok (e2', _, _) ->
          (* Synthesize the face types based on what was inferred *)
          begin match eval ind_env ety with
          | Pi(i, Int(), ty') ->
            let ty0 = Expr.open_var 0 (I0()) ty' in
            let ty1 = Expr.open_var 0 (I1()) ty' in
            let elabi0 = elaborate global ind_env ctx lvl sl ty0 (ph+1) vars (eval ind_env (App(e', I0()))) in
            let elabi1 = elaborate global ind_env ctx lvl sl ty1 (ph+1) vars (eval ind_env (App(e', I1()))) in
            begin match elabi0, elabi1 with
            | Ok (ei0, _, sa), Ok (ei1, _, _) ->
              (* Typecheck the i face of the tubes *)
              let elab1i0 = elaborate global ind_env ctx lvl sl ty0 (ph+1) vars (eval ind_env (App(e1', i1))) in
              let elab2i1 = elaborate global ind_env ctx lvl sl ty1 (ph+1) vars (eval ind_env (App(e2', i1))) in
              begin match elab1i0, elab2i1 with
              | Ok (e1i0, _, sa1), Ok (e2i0, _, sa2) ->
                let u1 = unify global ind_env ctx lvl sl (ph+1) vars (eval ind_env ei0, e1i0, ty0) false in
                let u2 = unify global ind_env ctx lvl sl (ph+1) vars (eval ind_env ei1, e2i0, ty1) false in
                begin match u1, u2 with
                | Ok _, Ok _ ->
                  Ok (Hcom(i1, j1, e', e1', e2'), Pi(i, Int(), ty'), Stack.lappend sa sa1 sa2)
                | Error (_, msg), _ ->
                  Error (Stack.lappend sa sa1 sa2,
                  "Invalid composition scenario: Error when unifying the i0-endpoint of the lid \n  " ^ 
                  Pretty.printf (eval ind_env ei0) ^ "\nwith the " ^ Pretty.printf i1 ^ "-endpoint of the i0-tube \n  " ^ Pretty.printf (eval ind_env e1i0) ^
                  "\n" ^ msg)
                | _, Error (_, msg) -> 
                  Error (Stack.lappend sa sa1 sa2, 
                    "Invalid composition scenario: Error when unifying the terms\n  " ^ 
                    Pretty.printf (eval ind_env ei1) ^ "\nwith the " ^ Pretty.printf i1 ^ "-endpoint of the i1-tube \n  " ^ Pretty.printf (eval ind_env e2i0) ^
                    "\n" ^ msg)
                end
              | Error (sa, msg), _ -> 
                Error (sa, "Error when synthesizing type for the homogeneous filling\n  " ^ Pretty.printf (Hcom(i1, j1, e', e1', e2')) ^ 
                    "\nThe i0-face of the i0-tube\n  " ^ Pretty.printf (eval ind_env (App(e1', I0()))) ^ "\ndoes not have the expected type\n  " ^ Pretty.printf ty0 ^ 
                    "\n" ^ msg)
              | _, Error (sa, msg) ->
                Error (sa, "Error when synthesizing type for the homogeneous filling\n  " ^ Pretty.printf (Hcom(i1, j1, e', e1', e2')) ^ 
                    "\nThe i0-face of the i1-tube\n  " ^ Pretty.printf (eval ind_env (App(e1', I0()))) ^ "\ndoes not have the expected type\n  " ^ Pretty.printf ty0 ^ 
                    "\n" ^ msg)
              end
            | Error (sa', msg), _ ->
              Error (Stack.append ss sa', 
                "Failed to synthesize placeholder type. The lid " ^ Pretty.printf e' ^ " has type " ^ Pretty.printf ety ^ 
                ", but could not check that the line\n  " ^ Pretty.printf (eval ind_env (App(e', I1()))) ^ "\nhas type\n  " ^ Pretty.printf ty' ^
                "\nin the homogeneous filling\n  hfill (" ^ Pretty.printf e' ^ 
                ")\n    | i0 → " ^ Pretty.printf e1' ^
                "\n    | i1 → " ^ Pretty.printf e2' ^ "\n" ^ msg)
            | _, Error msg -> Error msg
            end
          | _ -> Error (sl, "The lid of the homogeneous filling\n  " ^ Pretty.printf e ^ 
            "\nis expected to have the function type but has type\n  " ^ Pretty.printf ety)
          end
        | Error msg, _, _ | _, Error msg, _ | _, _, Error msg -> 
          Error msg
        end
        
      | _, _ ->
        Error (sl, "The homogeneous composition " ^ Pretty.printf (Hcom(i1, j1, e, e1, e2)) ^ 
          "\nhas type\n  " ^ Pretty.printf (Pi(k, int, ty')) ^
          "\nbut is expected to have type\n  I → ?0?")
      end
    
    | ty ->
      Error (sl, "The homogeneous composition\n  " ^ Pretty.printf (Hcom(i1, j1, e, e1, e2)) ^ 
      "\nis expected to have type\n  I → I → ?0?\nand not\n  " ^ Pretty.printf ty)
    end

  | Pabs (i, e) ->
    let e = eval ind_env e in
    let ty = eval ind_env ty in
    let h0 = Placeholder.generate ph [] in
    let elabt = elaborate global ind_env ctx lvl sl h0 (ph+1) vars ty in
    begin match elabt with
    | Ok (Pathd (Hole (n, l), e1, e2), _, _) ->
      let v1 = Expr.init_fresh vars in
      let h0 = Placeholder.generate (ph+1) [] in
      let ei = Expr.open_var 0 (Global v1) e in
      let elab = elaborate global ind_env ((v1, Int(), true) :: ctx) lvl sl (Hole (n, l)) (ph+2) (vars+1) ei in

      begin match elab with
      | Ok (e', _, sa) ->
        let e_closed = Expr.close_bound v1 e' in
        let ei0 = Expr.open_var 0 (I0()) e_closed in
        let ei1 = Expr.open_var 0 (I1()) e_closed in
        let elab1 = elaborate global ind_env ((v1, Int(), true) :: ctx) lvl sl h0 (ph+2) (vars+1) ei0 in
        let elab2 = elaborate global ind_env ((v1, Int(), true) :: ctx) lvl sl h0 (ph+2) (vars+1) ei1 in
        begin match elab1, elab2 with
        | Ok (ei0, tyi0, _), Ok (ei1, tyi1, _) ->
        
          let u1 = unify global ind_env ctx lvl sl (ph+2) (vars+1) (eval ind_env ei0, eval ind_env e1, tyi0) false in
          let u2 = unify global ind_env ctx lvl sl (ph+2) (vars+1) (eval ind_env ei1, eval ind_env e2, tyi1) false in
          begin match u1, u2 with
          | Ok ui0, Ok ui1 ->
            let v2 = Expr.init_fresh vars in
            let ty' = Expr.fullsubst 0 (I0()) (Global v2) true tyi0 in
            let ty'' = Expr.fullsubst 0 (I1()) (Global v2) true tyi1 in
            let elabTy = elaborate global ind_env ctx lvl sl h0 (ph+2) (vars+2) ty in

            begin match elabTy with
            | Ok (_, tTy, _) ->
              let u = unify global ind_env ctx lvl sl (ph+2) (vars+2) (ty', ty'', tTy) false in
              begin match u with
              | Ok st ->
                Ok (Pabs (i, e_closed), Pathd (Lam(v2, st), ui0, ui1), sa)
              | Error (_, msg) -> 
                Error (sa, 
                "Type unification error in path abstraction.\n" ^ msg)
              end

            | Error (sa', msg) -> (* This case is impossible *)
              Error (Stack.append sa sa', 
              "Typehood error in path abstraction.\n" ^ msg)
            end
          | _ , Ok _ ->
            Error (sa, "Error in path abstraction over " ^ i ^ ": I. Failed to unify\n  " ^
                    Pretty.printf e1 ^ "\nwith\n  " ^ Pretty.printf ei0 ^ "≡ " ^ Pretty.printf e ^ "[i0/" ^ i ^ "]" ^ "\n" ^
                    goal_msg ctx (Pabs (i, e')) ty) 
          | _ ->
            Error (sa, "Failed to unify\n  " ^ 
                    Pretty.printf e2 ^ "\nwith\n  " ^ Pretty.printf ei1 ^ "≡ " ^ Pretty.printf e ^ "[i1/" ^ i ^ "]" ^ "\n" ^
                    goal_msg ctx (Pabs (i, e')) ty)
          end
        | Error (_, msg), _| _, Error (_, msg) -> 
          Error (sa, "Failed synthetization of type placeholder for i0-endpoint in path abstraction.\n" ^ msg)
        end
      | Error (sa, msg) -> 
        Error (sa, "Failed synthetization of type placeholder for i0-endpoint in path abstraction.\n" ^ msg)
      end
    | Ok (Pathd (ty1, e1, e2), _, _) ->
      let v1 = Expr.init_fresh vars in
      let ei = Expr.open_var 0 (Global v1) e in
      let ty1' = eval ind_env (App(ty1, Global v1)) in
      let elab = elaborate global ind_env ((v1, Int(), true) :: ctx) lvl sl ty1' (ph+1) (vars+1) ei in
      begin match elab with
      | Ok (e', _, saa) ->
        let e_closed = Expr.close_bound v1 e' in
        let ei0 = eval ind_env (Expr.open_var 0 (I0()) e_closed) in
        let ei1 = eval ind_env (Expr.open_var 0 (I1()) e_closed) in
        let elab1 = elaborate global ind_env ctx lvl sl (eval ind_env (App(ty1, I0()))) (ph+1) (vars+1) ei0 in
        let elab2 = elaborate global ind_env ctx lvl sl (eval ind_env (App(ty1, I1()))) (ph+1) (vars+1) ei1 in
        begin match elab1, elab2 with
        | Ok (ei0, tyi0, _), Ok (ei1, tyi1, _) ->
          let ei0' = eval ind_env ei0 and e1' = eval ind_env e1 in
          let ei1' = eval ind_env ei1 and e2' = eval ind_env e2 in
          let u1 = unify global ind_env ctx lvl sl (ph+1) vars (ei0', e1', tyi0) false in
          let u2 = unify global ind_env ctx lvl sl (ph+1) vars (ei1', e2', tyi1) false in
          begin match u1, u2 with
          | Ok ui0, Ok ui1 -> 
            Ok (Pabs (i, e_closed), Pathd (ty1, ui0, ui1), saa)
          | Error ((s,s'), msg) , Ok _ ->
            begin match s, s' with
            | At(s',I0()), s | s, At(s',I0()) ->
              let h1 = Placeholder.generate (ph+1) [] in
              let elab0 = elaborate global ind_env ctx lvl sl h1 (ph+2) vars s' in
              begin match elab0 with
              | Ok (_, Pathd(sty, sa, _), _) ->
                let u = unify global ind_env ctx lvl sl (ph+2) vars (s, sa, eval ind_env (App(sty, I0()))) false in
                begin match u with
                | Ok _ ->
                  Ok (Pabs (i, e_closed), Pathd (ty1, ei0, ei1), saa)
                | Error (_, msg) ->
                  Error (saa, "Error in path abstraction over " ^ i ^ " : I when attempting unification at the i0-endpoint. Failed to unify\n  " ^
                  Pretty.printf e1 ^ "\nwith\n  " ^ Pretty.printf ei0 ^ "≡ " ^ Pretty.printf e' ^ "[i0/" ^ i ^ "]" ^ "\n" ^
                  msg ^ "\n" ^ goal_msg ctx (Pabs (i, e')) ty )
                end
              | _ -> 
                Error (saa, "Error in path abstraction over " ^ i ^ " : I when attempting unification at the i0-endpoint. Failed to unify\n  " ^ 
                        Pretty.printf e1 ^ "\nwith\n  " ^ Pretty.printf ei0 ^ "≡ " ^ Pretty.printf e' ^ "[i0/" ^ i ^ "]" ^ "\n" ^
                        msg ^ "\n" ^ goal_msg ctx (Pabs (i, e')) ty)
              end
            | _ ->
              Error (saa, "Failed to unify\n  " ^ 
                    Pretty.printf e1 ^ "\nwith\n  " ^ Pretty.printf ei0 ^ "≡ " ^ Pretty.printf e' ^ "[i0/" ^ i ^ "]" ^ "\n" ^
                    msg ^ "\n" ^ goal_msg ctx (Pabs (i, e')) ty)
            end
          | _ , Error ((s,s'), msg) ->
            begin match s, s' with
            | At(s',I1()), s | s, At(s',I1()) ->
              let h1 = Placeholder.generate (ph+1) [] in
              let elab0 = elaborate global ind_env ctx lvl sl h1 (ph+2) vars s' in
              begin match elab0 with
              | Ok (_, Pathd(sty,_,sb), _) ->
                let u = unify global ind_env ctx lvl sl (ph+2) vars (s, sb, eval ind_env (App(sty, I1()))) false in
                begin match u with
                | Ok _ -> 
                  Ok (Pabs (i, e_closed), Pathd (ty1, ei0, ei1), saa)
                | Error (_, msg) ->
                  Error (saa, "Error in path abstraction over " ^ i ^ " : I when attempting unification at the i1-endpoint. Failed to unify\n  " ^ 
                    Pretty.printf e2 ^ "\nwith\n  " ^ Pretty.printf ei1 ^ "≡ " ^ Pretty.printf e' ^ "[i1/" ^ i ^ "]" ^ "\n" ^
                    msg ^ "\n" ^ goal_msg ctx (Pabs (i, e')) ty )
                end

              | _ -> 
                Error (saa, "Failed to unify\n  " ^ 
                        Pretty.printf e2 ^ "\nwith\n  " ^ Pretty.printf ei1 ^ "≡ " ^ Pretty.printf e' ^ "[i1/" ^ i ^ "]" ^ "\n" ^
                        msg ^ "\n" ^ goal_msg ctx (Pabs (i, e')) ty )
              end
            | _ ->
              Error (saa, "Unification error at path abstraction. Failed to unify\n  " ^
                    Pretty.printf e2 ^ "\nwith\n  " ^ Pretty.printf ei1 ^ "≡ " ^ Pretty.printf e' ^ "[i1/" ^ i ^ "]" ^ 
                    "\n" ^  Pretty.printf ei1' ^ "\n" ^  Pretty.printf e2' ^
                    "\n" ^ msg ^ "\n" ^ goal_msg ctx (Pabs (i, e')) ty )
            end
          end

        | Error (_, msg), _ ->
          Error (saa, "Error when checking that the path abstracted term\n  " ^ 
            Pretty.printf (Pabs(i, eval ind_env e)) ^ "\nhas type\n  " ^ Pretty.printf ty ^ 
            "\nThe i0-endpoint\n  " ^ Pretty.printf (eval ind_env (Expr.open_var 0 (I0()) e')) ^ 
            "\ndoes not have type\n  " ^ Pretty.printf (eval ind_env (App(ty1, I0()))) ^
            "\n" ^ msg)
        | _, Error (_, msg) -> 
          Error (saa, "Error when checking that the path abstracted term\n  " ^ 
            Pretty.printf (Pabs(i, eval ind_env e)) ^ "\nhas type\n  " ^ Pretty.printf ty ^ 
            "\nThe i1-endpoint\n  " ^ Pretty.printf (eval ind_env (Expr.open_var 0 (I1()) e')) ^ 
            "\ndoes not have type\n  " ^ Pretty.printf (eval ind_env (App(ty1, I1()))) ^ 
            "\n" ^ msg)
        end
      | Error (sa, msg) -> 
        Error (sa, "Error in the body of path abstraction: failed to check that the body " ^ 
          Pretty.printf ei ^ "\nhas type\n  " ^ Pretty.printf ty1' ^ "\n" ^ msg)
      end
    | Ok (Hole _, _, _) ->
      let h1 = Placeholder.generate (ph+1) [] in
      let ei0 = Expr.open_var 0 (I0()) e in
      let ei1 = Expr.open_var 0 (I1()) e in
      let elab0 = elaborate global ind_env ctx lvl sl h1 (ph+2) vars ei0 in
      let elab1 = elaborate global ind_env ctx lvl sl h1 (ph+2) vars ei1 in
      begin match elab0, elab1 with
      | Ok (_, tyi0, _), Ok (_, tyi1, _) ->
        let v1 = Expr.init_fresh vars in
        let ty' = Expr.fullsubst 0 (I0()) (Global v1) true tyi0 in
        let ty'' = Expr.fullsubst 0 (I1()) (Global v1) true tyi1 in
        begin match elaborate global ind_env ctx lvl sl h1 (ph+2) (vars+1) ty' with
        | Ok (ty', tTy', _) ->
          let u = unify global ind_env ctx lvl sl (ph+2) (vars+1) (ty', ty'', tTy') false in
          begin match u with
          | Ok st ->
            elaborate global ind_env ctx lvl sl (Pathd(Lam(v1,st), ei0, ei1)) (ph+2) (vars+1) (Pabs (i, e))
          | Error (_, msg) ->
            Error (sl, "Failed to unify the types\n  " ^ Pretty.printf ty' ^ "\nand\n  " ^ Pretty.printf ty'' ^ "\n" ^ msg)
            
          end
        | Error msg -> (* This case never occurs *)
          Error msg
        end
      | Error msg, _ | _, Error msg -> Error msg
      end
    | Ok (ty', _, sa) -> 
      Error (sa, "The expression\n  <" ^ i ^ "> " ^ Pretty.printf e ^ "\nchecked against type " ^ Pretty.printf ty ^ " is expected to have type\n  pathd ?0? ?1? ?2?\nbut has type\n  " ^ Pretty.printf ty')
    | Error (sa, msg) -> 
      Error (sa, "Failed to prove that\n  " ^ Pretty.printf (eval ind_env ty) ^ "\nis a type\n" ^ msg)
    end
  
  | At (e1, e2) ->
    let h1 = Placeholder.generate ph [] in
    let h2 = Placeholder.generate (ph+1) [] in
    let h3 = Placeholder.generate (ph+2) [] in
    let elab1 = elaborate global ind_env ctx lvl sl (Pathd(h1, h2, h3)) (ph+3) vars e1 in
    let elab2 = elaborate global ind_env ctx lvl sl (Int()) (ph+3) vars e2 in
    begin match elab1, elab2 with
    | Ok (e1', ty1', sa1), Ok (e2', _, sa2) ->
      begin match ty1' with
      | Pathd (ty', a, b) ->
        if e2' = I0() then (* TODO: better as pattern matching *)
          match a, ty' with
          | Hole _, Lam(_, ty') -> (* unify ty' and ty*)
            Ok (At (e1', I0()), Expr.open_var 0 (I0()) ty', Stack.append sa1 sa2)
          | Hole _, Hole _ -> 
            Ok (At (e1', I0()), ty, Stack.append sa1 sa2)
          | Hole _, ty' -> 
            Ok (At (e1', I0()), App(ty', I0()), Stack.append sa1 sa2)
          | _ -> 
            elaborate global ind_env ctx lvl sl ty (ph+3) vars a
        else if e2' = I1() then
          match b, ty' with
          | Hole _, Lam(_, ty') -> 
            Ok (At (e1', I1()), Expr.open_var 0 (I1()) ty', Stack.append sa1 sa2)
          | Hole _, Hole _ -> 
            Ok (At (e1', I1()), ty, Stack.append sa1 sa2)
          | Hole _, ty' -> 
            Ok (At (e1', I1()), App(ty', I1()), Stack.append sa1 sa2)
          | _ -> 
            elaborate global ind_env ctx lvl sl ty (ph+3) vars b
        else
          begin match ty' with
          | Lam(_, ty') ->
            let ty2' = Expr.open_var 0 e2' ty' in
            let elabTy = elaborate global ind_env ctx lvl sl h1 (ph+3) vars ty2' in
            begin match elabTy with
            | Ok (_, tTy, _) ->
              let u = unify global ind_env ctx lvl sl (ph+3) vars (ty2', ty, tTy) false in
              begin match u with
              | Ok tty -> Ok (At (e1', e2'), tty, Stack.append sa1 sa2)
              | _ -> 
                Error (Stack.append sa1 sa2, 
                  "Failed to unify\n  " ^ 
                  Pretty.printf ty2' ^ "\nwith\n  " ^ Pretty.printf ty)
              end
            | Error msg -> (* This case is impossible *)
              Error msg
            end
            
          | _ -> 
            begin match ty with
            | App(ty, i) ->
              let elabTy = elaborate global ind_env ctx lvl sl h1 (ph+3) vars ty' in
              begin match elabTy with
              | Ok (_, tTy, _) ->
                let u = unify global ind_env ctx lvl sl (ph+3) vars (ty', ty, tTy) false in
                begin match u, e2 = i with 
                | Ok tty, true -> 
                  Ok (At (e1', e2'), App(tty, i), Stack.append sa1 sa2)
                | _ -> 
                  Error (Stack.append sa1 sa2, 
                    "Failed to unify\n  " ^ 
                    Pretty.printf ty' ^ "\nwith\n  " ^ Pretty.printf ty)
                end
              | Error msg -> (* This case is impossible *)
                Error msg
              end
            | ty ->
              let elabTy = elaborate global ind_env ctx lvl sl h1 (ph+3) vars ty' in
              begin match elabTy with
              | Ok (_, tTy, _) ->
                let u = unify global ind_env ctx lvl sl (ph+3) vars (ty', ty, tTy) false in
                begin match u with
                | Ok tty -> 
                  Ok (At (e1', e2'), tty, Stack.append sa1 sa2) 
                | _ -> 
                  Error (Stack.append sa1 sa2, "Failed to unify\n  " ^ 
                  Pretty.printf ty' ^ "\nwith\n  " ^ Pretty.printf ty)
                end
              | Error msg -> (* This case is impossible *)
                Error msg
              end
            end
          end
      | _ -> 
        Error (Stack.append sa1 sa2, 
          "Type mismatch when checking that\n  " ^ Pretty.printf e1' ^ 
          "\nof type\n  " ^ Pretty.printf ty1' ^ "\nhas type\n  pathd ?0? ?1? ?2? ")
      end
    | Error msg, _ | _, Error msg -> 
      Error msg
    end

  | Pi(x, ty1, ty2) ->
    let ty1 = eval ind_env ty1 in
    let h1 = Placeholder.generate ph [] in
    let elab1 = elaborate global ind_env ctx lvl sl h1 (ph+1) vars ty1 in
    let ty2 = eval ind_env ty2 in
    let ty2' = (Expr.open_var 0 (Global x) ty2) in
    let elab2 = elaborate global ind_env ((x, ty1, true) :: ctx) lvl sl h1 (ph+1) vars ty2'
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
          Error (Stack.append sa1 sa2, 
            "Universe level mismatch when checking that the type\n  " ^ Pretty.printf (Pi(x, ty1, ty2)) ^
            "\nof type \n  " ^ Pretty.printf (Type max) ^ "\nhas type\n  " ^ Pretty.printf (Type m))
      | Hole _ -> 
        Ok (Pi(x, ty1', Expr.close_bound x ty2'), Type max, Stack.append sa1 sa2)
      | _ ->
        Error (Stack.append sa1 sa2, 
          "Type mismatch when checking that\n  " ^ Pretty.printf (Pi(x, ty1, ty2)) ^ "\nhas type\n  " ^ Pretty.printf ty)
      end

    | Ok (ty1', Type n, sa), Ok (Hole (k,l), _, _) -> 
      begin match ty with
      | Type m ->
        if Level.leq n m then 
          Ok (Pi(x, ty1', Hole (k,l)), Type m, sa) 
        else 
          Error (sa, "Type mismatch when checking that the type\n  " ^ Pretty.printf (Pi(x, ty1, ty2)) ^ 
            "\nof type \n  " ^ Pretty.printf (Type n) ^ "\nhas type\n  " ^ Pretty.printf (Type m))
      | Hole _ -> 
        Ok (Pi(x, ty1', Hole (k,l)), Type n, sa) (* TODO: hole might have live in a higher universe *)
      | _ ->
        Error (sa, "Type mismatch when checking that\n  " ^ Pretty.printf (Pi(x, ty1, ty2)) ^ "\nhas type\n  " ^ Pretty.printf ty)
      end
    | Ok (Hole (k,l), _, _), Ok (ty2', Type n, sa) -> 
      begin match ty with
      | Type m ->
        if Level.leq n m then 
          Ok (Pi(x, Hole (k,l), Expr.close_bound x ty2'), Type m, sa) 
        else 
          Error (sa, "Type mismatch when checking that \n  " ^ Pretty.printf (Pi(x, ty1, ty2)) ^ 
                "\nof type \n  " ^ Pretty.printf (Type n) ^ "\n has type\n  " ^ Pretty.printf (Type m))
      | Hole _ -> 
        Ok (Pi(x, Hole (k,l), Expr.close_bound x ty2'), Type n, sa) (* TODO: hole might have live in a higher universe *)
      | _ ->
        Error (sa, "Type mismatch when checking that\n  " ^ Pretty.printf (Pi(x, ty1, ty2)) ^ "\nhas type\n  " ^ Pretty.printf ty)
      end
    | Ok (Hole (k1,l1), _, _), Ok (Hole (k2,l2), _, _) ->
      begin match ty with
      | Type m -> 
          Ok (Pi(x, Hole (k1,l1), Hole (k2,l2)), Type m, sl) 
      | Hole (k, l) -> 
          Ok (Pi(x, Hole (k1,l1), Hole (k2,l2)), Hole(k, l), sl)
      | _ ->
        Error (sl, "Type mismatch when checking that the type\n  " ^ Pretty.printf (Pi(x, ty1, ty2)) ^ "\nhas type\n  " ^ Pretty.printf ty)
      end
    
    | Ok (_, Type _, sa), Error (sb, msg) -> 
      Error (Stack.append sa sb, "Failed to check that the codomain\n  " ^ Pretty.printf (eval ind_env ty2') ^ "\nis a type\n" ^ msg)
    | _, Error (sb, msg) -> 
      Error (sb, "Failed to check that the codomain\n  " ^ Pretty.printf (eval ind_env ty2') ^ "\nis a type\n" ^ msg)
    | Error (sa, msg), _ -> 
      Error (sa, "Failed to check that the domain\n  " ^ Pretty.printf (eval ind_env ty1) ^ "\nis a type\n" ^ msg)
    | Ok (ty1', u1, _), Ok (ty2', u2, _) -> 
      Error (sl, "Failed to show that the dependent function " ^ Pretty.printf (Pi(x, ty1, ty2)) ^ " has the expected type " ^ Pretty.printf ty ^ ". Can only check that\n  " ^ Pretty.printf ty1' ^ "\nhas type " ^ Pretty.printf u1 ^
        "\nand that\n  " ^ Pretty.printf ty2' ^ "\nhas type " ^ Pretty.printf u2)
    end
  
  | Sigma(x, ty1, ty2) ->
    let ty1 = eval ind_env ty1 in
    let h1 = Placeholder.generate ph [] in
    let elab1 = elaborate global ind_env ctx lvl sl h1 (ph+1) vars ty1 in
    let ty2 = eval ind_env ty2 in
    let elab2 = elaborate global ind_env ((x, ty1, true) :: ctx) lvl sl h1 (ph+1) vars (Expr.open_var 0 (Global x) ty2)
    in
    begin match elab1, elab2 with
    | Ok (ty1', Type n1, sa1), Ok (ty2', Type n2, sa2) ->
      let max = Level.reduce (Max(n1, n2)) in
      begin match ty with
      | Type (Var par) when Level.is_arbitrary_string par ->
        (* Synthesize type levels placeholder *)
        Ok (Sigma(x, ty1', Expr.close_bound x ty2'), Type (Suc(max)), Stack.append sa1 sa2)
      | Type m -> 
        (* Check if levels are compatible *)
        if Level.leq max m then 
          Ok (Sigma(x, ty1', Expr.close_bound x ty2'), Type m, Stack.append sa1 sa2) 
        else 
          Error (Stack.append sa1 sa2, "Type mismatch when checking that \n  Σ ( " ^ x ^ " : " ^ Pretty.printf ty1 ^ ") " ^ Pretty.printf ty2 ^ 
            "\nof type \n  " ^ Pretty.printf (eval ind_env (Type (Max(n1, n2)))) ^ "\n has type\n  " ^ Pretty.printf (Type m))
      | Hole _ -> 
        Ok (Sigma(x, ty1', Expr.close_bound x ty2'), Type max, Stack.append sa1 sa2)
      | _ ->
        Error (Stack.append sa1 sa2, "Type mismatch when checking that\n  Σ ( " ^ x ^ " : " ^ 
          Pretty.printf ty1 ^ ") " ^ Pretty.printf ty2 ^ "\nhas type\n  " ^ Pretty.printf ty)
      end
    
    | Ok (ty1', Type n, sa), Ok (Hole (k,l), _, _) -> 
      begin match ty with
      | Type m ->
        if Level.leq n m then 
          Ok (Sigma(x, ty1', Hole (k,l)), Type m, sa) 
        else 
          Error (sa, "Type mismatch when checking that \n  Σ ( " ^ x ^ " : " ^ Pretty.printf ty1 ^ ") " ^ Pretty.printf ty2 ^ 
                "\nof type \n  " ^ Pretty.printf (Type n) ^ "\n has type\n  " ^ Pretty.printf (Type m))
      | Hole _ -> 
        Ok (Sigma(x, ty1', Hole (k,l)), Type n, sa) (* TODO: hole might have live in a higher universe *)
      | _ ->
        Error (sa, "Type mismatch when checking that\n  Σ ( " ^ x ^ " : " ^ Pretty.printf ty1 ^ ") " ^ Pretty.printf ty2 ^ "\nhas type\n  " ^ Pretty.printf ty)
      end
    | Ok (Hole (k,l), _, _), Ok (ty2', Type n, sa) -> 
      begin match ty with
      | Type m -> 
        if Level.leq n m then 
          Ok (Sigma(x, Hole (k,l), Expr.close_bound x ty2'), Type m, sa) 
        else 
          Error (sa, "Type mismatch when checking that \n  Σ ( " ^ x ^ " : " ^ Pretty.printf ty1 ^ ") " ^ Pretty.printf ty2 ^ 
                "\nof type \n  " ^ Pretty.printf (Type n) ^ "\n has type\n  " ^ Pretty.printf (Type m))
      | Hole _ -> 
        Ok (Sigma(x, Hole (k,l), Expr.close_bound x ty2'), Type n, sa) (* TODO: hole might have live in a higher universe *)
      | _ ->
        Error (sa, "Type mismatch when checking that\n  Σ ( " ^ x ^ " : " ^ Pretty.printf ty1 ^ ") " ^ Pretty.printf ty2 ^ "\nhas type\n  " ^ Pretty.printf ty)
      end
    | Ok (Hole (k1,l1), _, _), Ok (Hole (k2,l2), _, _) ->
      begin match ty with
      | Type m ->
          Ok (Sigma(x, Hole (k1,l1), Hole (k2,l2)), Type m, sl)
      | Hole (k, l) ->
          Ok (Sigma(x, Hole (k1,l1), Hole (k2,l2)), Hole(k, l), sl)
      | _ ->
        Error (sl, 
        "Type mismatch when checking that\n  Σ ( " ^ x ^ " : " ^ Pretty.printf ty1 ^ ") " ^ Pretty.printf ty2 ^ "\nhas type\n  " ^ Pretty.printf ty)
      end
    | Ok (_, Type _, _), Error (sa, msg) ->
      Error (sa, "Failed to check that\n  " ^ Pretty.printf ty2 ^ "\nis a type\n" ^ msg)
    | Error (sa, msg), _ -> Error (sa, "Failed to check that\n  " ^ Pretty.printf ty1 ^ "\nis a type\n" ^ msg)
    | _ -> Error (sl, "Failed to check that\n  " ^ Pretty.printf ty1 ^ "\nis a type")
    end
  
  | Int() ->
    let ty = eval ind_env ty in
    begin match ty with
    | Type m -> 
      Ok (Int(), Type m, sl)
    | Hole _ -> 
      Ok (Int(), Type (Num 0), sl)
    | _ -> 
      Error (sl, "Type mismatch when checking that\n  I\nhas type\n  " ^ Pretty.printf ty)
    end

  | Void() ->
    let ty = eval ind_env ty in
    begin match ty with
    | Type m -> Ok (Void(), Type m, sl)
    | Hole _ -> Ok (Void(), Type (Num 0), sl)
    | _ -> Error (sl, "Type mismatch when checking that\n  void\n has type\n  " ^ Pretty.printf ty)
    end

  | Pathd(ty1, e1, e2) ->
    let h1 = Placeholder.generate ph [] in
    let ty = eval ind_env ty in
    (* First consider the inference case: the type line is a placeholder *)
    begin match ty1 with
    (* Subcase 1: dependent type placeholder *)
    | Hole (n,l) ->
      begin match e1, e2 with 
      | Hole (n1,l1), Hole (n2,l2) ->
          begin match ty with
          | Type m ->
            Ok (Pathd(Hole (n,l), Hole (n1,l1), Hole (n2,l2)), Type m, sl)
          | Hole (m,k) ->
            Ok (Pathd(Hole (n,l), Hole (n1,l1), Hole (n2,l2)), Hole (m,k), sl)
          | _ -> 
            Error (sl, "Failed to check that\n  " ^ Pretty.printf ty ^ "\nis a type")
          end
      | _ ->
        (* Neither endpoint is a placeholder *)
        let elab1 = elaborate global ind_env ctx lvl sl h1 (ph+1) vars e1 in
        let elab2 = elaborate global ind_env ctx lvl sl h1 (ph+1) vars e2 in
        begin match elab1, elab2 with
        | Ok (e1', tye1, sa1), Ok (e2', tye2, sa2) ->
          let tye1 = eval ind_env tye1 in
          let tye2 = eval ind_env tye2 in
          begin match ty, tye1, tye2 with
          (* Target type has been specified *)
          | Type m, tye1, Hole _ ->
            let v1 = Expr.init_fresh vars in
            let tyei = Pi(v1, Int(), Expr.fullsubst 0 (I0()) (Local 0) true tye1) in
            Ok (Pathd(tyei, e1', e2'), Type m, Stack.append sa1 sa2)
          | Type m, _ , tye2 -> 
            let v1 = Expr.init_fresh vars in
            let tyei = Pi(v1, Int(), Expr.fullsubst 0 (I1()) (Local 0) true tye2) in
            Ok (Pathd(tyei, e1', e2'), Type m, Stack.append sa1 sa2)
          (* Target type is a placeholder *)
          | Hole _, tye1, Hole _ ->
            let v1 = Expr.init_fresh vars in
            let tyei = Pi(v1, Int(), Expr.fullsubst 0 (I0()) (Local 0) true tye1) in
            let h2 = Placeholder.generate (ph+1) [] in
            begin match elaborate global ind_env ctx lvl sl h2 (ph+2) vars tye1 with
            | Ok (_, tTye1, _) ->
                Ok (Pathd(tyei, e1', e2'), tTye1, Stack.append sa1 sa2)
            | Error (_, msg) ->
              Error (Stack.append sa1 sa2, "Failed to check that\n  " ^ Pretty.printf tye1 ^ "\nis a type\n" ^ msg)
            end
          | Hole _, _, tye2 -> 
            let v1 = Expr.init_fresh vars in
            let tyei = Pi(v1, Int(), Expr.fullsubst 0 (I1()) (Local 0) true tye2) in
            let h2 = Placeholder.generate (ph+1) [] in
            begin match elaborate global ind_env ctx lvl sl h2 (ph+2) vars tye2 with
            | Ok (_, tTye2, _) ->
                Ok (Pathd(tyei, e1', e2'), tTye2, Stack.append sa1 sa2)
            | Error (_, msg) ->
              Error (Stack.append sa1 sa2, "Failed to check that\n  " ^ Pretty.printf tye1 ^ "\nis a type\n" ^ msg)
            end
          | _ -> 
            Error (Stack.append sa1 sa2, "Failed to check that\n  " ^ Pretty.printf ty ^ "\nis a type")
          end
        | _ -> 
          Error (sl, "Failed to check that\n  " ^ Pretty.printf e1 ^ "\nhas type\n ?0?")
        end
      end
      (* Subcase 2: Non-dependent type with placeholder *)
    | Lam(x, Hole (n,l)) ->
      begin match e1, e2 with 
      | Hole (n1,l1), Hole (n2,l2) ->
          begin match ty with
          | Type m ->
            Ok (Pathd(Lam(x, Hole (n,l)), Hole (n1,l1), Hole (n2,l2)), Type m, sl)
          | Hole (m,k) ->
            Ok (Pathd(Lam(x, Hole (n,l)), Hole (n1,l1), Hole (n2,l2)), Hole (m,k), sl)
          | _ -> 
            Error (sl, "Failed to check that\n  " ^ Pretty.printf ty ^ "\nis a type")
          end
      | _ ->
        (* Neither endpoint is a placeholder *)
        let elab1 = elaborate global ind_env ctx lvl sl h1 (ph+1) vars e1 in
        let elab2 = elaborate global ind_env ctx lvl sl h1 (ph+1) vars e2 in
        begin match elab1, elab2 with
        | Ok (e1', tye1', sa1), Ok (e2', tye2', sa2) ->
          (* Target type is well-specified *)
          begin match ty, tye1', tye2' with
          | Type m, tye1, Hole _ -> Ok (Pathd(Lam(x, tye1), e1', e2'), Type m, Stack.append sa1 sa2)
          | Type m, Hole _, tye2 -> Ok (Pathd(Lam(x, tye2), e1', e2'), Type m, Stack.append sa1 sa2)
          | Type m, tye1, _ ->
            Ok (Pathd(Lam(x, tye1), e1', e2'), Type m, Stack.append sa1 sa2)
          (* If target type is also a placeholder we pick a well-specified type of an endpoint*)
          | Hole _, tye1, Hole _ ->
            let h2 = Placeholder.generate (ph+1) [] in
            begin match elaborate global ind_env ctx lvl sl h2 (ph+2) vars tye1 with
            | Ok (tye1, tTye1, _) ->
                Ok (Pathd(Lam(x, tye1), e1', e2'), tTye1, Stack.append sa1 sa2)
            | Error (_, msg) ->
              Error (Stack.append sa1 sa2, "Failed to check that\n  " ^ Pretty.printf tye1 ^ "\nis a type\n" ^ msg)
            end  
          | Hole _, _, tye2 ->
            let h2 = Placeholder.generate (ph+1) [] in
            begin match elaborate global ind_env ctx lvl sl h2 (ph+2) vars tye2 with
            | Ok (tye2, tTye2, _) ->
              Ok (Pathd(Lam(x, tye2), e1', e2'), tTye2, Stack.append sa1 sa2)
            | Error (_, msg) ->
              Error (Stack.append sa1 sa2, "Failed to check that\n  " ^ Pretty.printf tye2 ^ "\nis a type\n" ^ msg)
            end
          | _ -> 
            Error (Stack.append sa1 sa2, "Failed to check that\n  " ^ Pretty.printf ty ^ "\nis a type")
            end
        | Ok _, Error (sa, msg) -> 
          Error (sa, "Failed to check that\n  " ^ Pretty.printf e2 ^ "\nhas type\n ?0?\n" ^ msg)
        | Error (sa, msg), _ -> 
          Error (sa, "Failed to check that\n  " ^ Pretty.printf e1 ^ "\nhas type\n " ^ Pretty.printf (Hole (n,l)) ^ "\n" ^ msg)
        end
      end
    (* Now consider the case where the type line is well-specified *)
    | ty1 ->
      let elabi0 = elaborate global ind_env ctx lvl sl h1 (ph+1) vars (eval ind_env (App (ty1, I0()))) in
      let elabi1 = elaborate global ind_env ctx lvl sl h1 (ph+1) vars (eval ind_env (App (ty1, I1()))) in
      begin match elabi0, elabi1 with
      | Ok (tyi0, tTyi0, _), Ok (tyi1, _, _) ->
        let elab = elaborate global ind_env ctx lvl sl h1 (ph+1) vars (eval ind_env ty1) in
        let elab1 = elaborate global ind_env ctx lvl sl tyi0 (ph+1) vars (eval ind_env e1) in
        let elab2 = elaborate global ind_env ctx lvl sl tyi1 (ph+1) vars (eval ind_env e2) in
        begin match elab, elab1, elab2 with
        | Ok (ty1', Pi(_, i, ty2), sa), Ok (e1', _, sa1), Ok (e2', _, sa2) ->
          begin match eval ind_env i, eval ind_env ty2 with
          | Int(), Type n | Hole _, Type n ->
            begin match ty with
            | Type m ->
              if Level.leq n m then 
                Ok (Pathd(ty1', e1', e2'), Type m, Stack.lappend sa sa1 sa2) 
              else if Level.is_arbitrary m then 
                Ok (Pathd(ty1', e1', e2'), Type n, Stack.lappend sa sa1 sa2)
              else 
                Error (Stack.lappend sa sa1 sa2, 
                  "Failed to check that\n  pathd " ^ 
                  Pretty.printf ty1' ^ " " ^  Pretty.printf e1' ^ " " ^  Pretty.printf e2' ^ 
                  "\nhas the expected type\n  " ^ Pretty.printf ty)
            | Hole _ -> 
              Ok (Pathd(ty1', e1', e2'), Type n, Stack.lappend sa sa1 sa2)
            | _ -> 
              Error (Stack.lappend sa sa1 sa2, 
              "Failed to check that\n  " ^ Pretty.printf ty2 ^ "\nis a type")
            end
          | Int() , Hole _ | Hole _, Hole _ -> 
            Ok (Pathd(ty1', e1', e2'), tTyi0, Stack.lappend sa sa1 sa2)
          | _ -> 
            Error (Stack.lappend sa sa1 sa2, "Failed to unify \n  " ^ Pretty.printf i ^ "with\n  I ")
          end
        | Ok (ty1', _, sa), Ok _, Ok _ ->
          Error (sa, "Type mismatch when checking that\n  " ^ Pretty.printf ty1' ^ "\nhas type\n  Π (v? : I) ?0?")
        | Error msg, _, _| _, Error msg, _ | _, _, Error msg -> 
          Error msg
        end
      | Error msg, _ | _, Error msg -> 
        Error msg
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
          Error (sl, "Universe inconsistency: the universe level of\n  " ^ Pretty.printf (Type n) ^ 
          "\nmust be inferior to the universe level of\n  " ^ Pretty.printf (Type m) ^ 
          "\nFailed to prove that " ^ Pretty.print_level n ^ " ≤ " ^ Pretty.print_level m)
      | Hole _ -> 
        Ok (Type n, Type (Suc n), sl)
      | _ -> 
        Error (sl, "Type mismatch when checking that\n  " ^ Pretty.printf (Type n) ^ 
          "\nhas type\n  " ^ Pretty.printf ty)
      end
    | Error msg -> 
      Error (sl, msg)
    end
  
  | Hole (n, l) ->
    Ok (Hole (n, l), ty, sl)

  | Wild n ->
    let solved, used = sl in
    (* If the placeholder has already synthesized replace it *)
    begin match List.find_opt (fun (n', _, _) -> n = n') solved with
    | Some (_, e', _) -> Ok (Global e', ty, sl)
    | None ->
      begin match find n global ind_env ctx ty lvl sl ph vars with (* false*)
      | Ok (e', ty') ->
        let sl' = ((n, e', ty') :: solved, used) in
        Ok (Global e', ty, sl')
      | Error _ -> 
        Error (([], []), 
        "Failed to synthesize placeholder for ?" ^ string_of_int n ^ "? in the current goal:\n" ^ 
        Global.printf ctx ^ "-------------------------------------------\n ⊢ " ^ Pretty.printf (eval ind_env ty))
      end
    end

  | Subgoal () ->
      Error (sl, 
      "The current goal:\n" ^ Global.printf ctx ^ 
      "-------------------------------------------\n ⊢ " ^ 
      Pretty.printf ty)

(* Finds a variable in a context for a given type up to unification *)

and find n global ind_env ctx ty lvl sl ph vars =
  let forbidden = snd sl in
  let rec search = function
    | [] -> Error "Can't find match"
    | (id, ty', _) :: ctx' ->
      if List.mem (n, id) forbidden then search ctx'
      else if ty' = ty then 
        Ok (id, ty) (* syntactic equality fast path *)
      else
        (* We ignore their types since they are assumed to be well-typed *)
        let h1 = Placeholder.generate ph [] in
        match unify global ind_env ctx lvl sl (ph+1) vars (ty, ty', h1) true with
        | Ok uty -> Ok (id, uty)
        | Error _ -> search ctx'
  in
  search ctx

(* Unifies two expressions at type *)

and unify global ind_env ctx lvl sl ph vars x lift =
  match x with
  | e, e', ty ->
    if e = e' then
      Ok e
    else
      match e, e', ty with
      | Hole (n1, l1), Hole (n2, l2), _ ->
        begin match l1, l2 with
        | [], [] -> Ok (Hole (n1, l1))
        | l1, [] -> Ok (Hole (n1, l1))
        | [], l2 -> Ok (Hole (n2, l2))
        | _ ->
          let rec common_el = function
          | [], [] -> Error()
          | _, [] | [], _ -> Error()
          | e :: l1 , e' :: l2 ->
            if List.mem e l2 then
              Ok e
            else if List.mem e' l1 then
              Ok e'
            else
              common_el (l1, l2)
          in
          match common_el (l1,l2) with
          | Ok e -> Ok e
          | Error() ->
            Error ((Hole (n1, l1), Hole (n2, l2)), 
                  "Failed to unify the placeholder\n  ?" ^ 
                  n1 ^ "?\nwhose suitable candidates are\n" ^ 
                  (String.concat " " (List.map (fun e -> Pretty.printf e) l1)) ^
                  "\nwith the placeholder\n  ?" ^ 
                  n2 ^ "?\nwhose suitable candidates are\n" ^ 
                  (String.concat " " (List.map (fun e -> Pretty.printf e) l2))) 
        end

      | e , _, Pathd(_, _, _) ->
        Ok e

      | e , Hole (n, l), _ | Hole (n, l), e, _ ->
        begin match l with
        | [] -> Ok e
        | _ ->
          let rec helper = function
          | [] -> false
          | e' :: l' -> e' = e || helper l' in
          let e_is_endpoint =
            let v = eval ind_env e in
            v = I0() || v = I1()
          in
          if helper l || e_is_endpoint then Ok e 
          else 
            Error ((e , Hole (n, l)),
                    "Failed to unify the placeholder\n  " ^ 
                    Pretty.printf (Hole (n, l)) ^ "\nwith the suitable candidates\n" ^ 
                    (String.concat " " (List.map Pretty.printf l)))
        end
      
      | Pi (_, ty1, ty2), Pi (_, ty1', ty2'), ty ->
        (* For now we just evaluate, soon we'll only evaluate if they are values *)
        let ty1 = eval ind_env ty1 in 
        let ty1' = eval ind_env ty1' in
        let u1 = unify global ind_env ctx lvl sl ph vars (ty1, ty1', ty) lift in
        begin match u1 with
        | Ok s1 -> 
          let v1 = Expr.init_fresh vars in
          let ty2_open = Expr.fullsubst 0 ty1 s1 true (Expr.open_bound (Global v1) ty2) in
          let ty2'_open = Expr.fullsubst 0 ty1' s1 true (Expr.open_bound (Global v1) ty2') in
          let ty2_open = eval ind_env ty2_open in
          let ty2'_open = eval ind_env ty2'_open in
          let u2 = unify global ind_env ((v1, s1, true) :: ctx) lvl sl ph (vars+1) (ty2_open, ty2'_open, ty) lift in
          begin match u2 with
          | Ok s2 -> 
            Ok (Pi (v1, s1, Expr.close_bound v1 s2))
          | Error msg -> 
            Error msg
          end
        | Error ((e1, e2), msg) -> Error ((e1, e2), "Unification failed at function type: " ^ msg)
        end

      | Sigma (_, ty1, ty2), Sigma (_, ty1', ty2'), ty ->
        let u1 = unify global ind_env ctx lvl sl ph vars (ty1, ty1', ty) lift in
        begin match u1 with
        | Ok s1 ->
          let v1 = Expr.init_fresh vars in
          let ty2_open = Expr.fullsubst 0 ty1 s1 true (Expr.open_bound (Global v1) ty2) in
          let ty2'_open = Expr.fullsubst 0 ty1' s1 true (Expr.open_bound (Global v1) ty2') in
          let u2 = unify global ind_env ((v1, s1, true) :: ctx) lvl sl ph (vars+1) (ty2_open, ty2'_open, ty) lift in
          begin match u2 with
          | Ok s2 -> Ok (Sigma (v1, s1, Expr.close_bound v1 s2))
          | Error (s, msg) -> Error (s, "Don't know how to unify the codomains of the dependent product type\n  " ^ Pretty.printf ty2_open ^ "\nwith\n  " ^ Pretty.printf ty2'_open ^ "\n" ^ msg)
          end
        | Error (s, msg) -> Error (s, "Don't know how to unify the domains of the dependent product type\n  " ^ Pretty.printf ty1 ^ "\nwith\n  " ^ Pretty.printf ty1' ^ "\n" ^ msg)
        end

      | Pathd (e, e1, e2) , Pathd (e', e1', e2'), ty ->
        let e = eval ind_env e and e' = eval ind_env e' in
        let e1 = eval ind_env e1 and e1' = eval ind_env e1' in
        let e2 = eval ind_env e2 and e2' = eval ind_env e2' in
        let u = unify global ind_env ctx lvl sl ph vars (e, e', Pi("v?", Int(), ty)) lift in
        let u1 = unify global ind_env ctx lvl sl ph vars (e1, e1', eval ind_env (App(e, I0()))) lift in
        let u2 = unify global ind_env ctx lvl sl ph vars (e2, e2', eval ind_env (App(e, I1()))) lift in
        begin match u, u1, u2 with
        | Ok s, Ok s1, Ok s2 -> 
          Ok (Pathd (s, s1, s2))

        | Error msg, _, _ | _ , Error msg, _ | _, _ , Error msg -> 
          Error (fst msg, "Don't know how to unify the dependent path types \n  " ^ Pretty.printf (Pathd (e, e1, e2)) ^ "\nand\n  " ^ Pretty.printf (Pathd (e', e1', e2')) ^ " due to the following errors:\n " ^ snd msg)
        end

      | Lam (x, e), Lam (x', e'), Pi(_, ty1 , ty2) ->
        if e = e' then
          Ok (Lam (x, e))
        else if Placeholder.is e' then
          Ok (Lam (x, e))
        else if Placeholder.is e then
          Ok (Lam (x, e'))
        else 
          begin match eval ind_env ty1 with
          | Int() | Hole(_,_) ->
            let h1 = Placeholder.generate ph [] in
            let elabt0 = elaborate global ind_env ctx lvl sl h1 (ph+1) vars (Expr.open_var 0 (I0()) ty2) in
            let elabt1 = elaborate global ind_env ctx lvl sl h1 (ph+1) vars (Expr.open_var 0 (I1()) ty2) in
            begin match elabt0, elabt1 with
            | Ok (tyi0, _, _), Ok (tyi1, _, _) ->
              let elab0 = elaborate global ind_env ctx lvl sl tyi0 (ph+1) vars (Expr.open_var 0 (I0()) e) in
              let elab0' = elaborate global ind_env ctx lvl sl tyi0 (ph+1) vars (Expr.open_var 0 (I0()) e') in
              let elab1 = elaborate global ind_env ctx lvl sl tyi1 (ph+1) vars (Expr.open_var 0 (I1()) e) in
              let elab1' = elaborate global ind_env ctx lvl sl tyi1 (ph+1) vars (Expr.open_var 0 (I1()) e') in
              begin match elab0, elab0', elab1, elab1' with
              | Ok (ei0, _, _), Ok (ei0', _, _), Ok (ei1, _, _), Ok (ei1', _, _) -> 
                let u0 = unify global ind_env ctx lvl sl (ph+1) vars (ei0, ei0', tyi0) lift in
                let u1 = unify global ind_env ctx lvl sl (ph+1) vars (ei1, ei1', tyi1) lift in
                begin match u0, u1 with
                | Ok _, Ok _ -> Ok (Lam (x, e))
                | Error msg, _ | _, Error msg -> Error msg
                end
              | Error (_, msg), _, _, _ | _, Error (_, msg), _, _ | _, _, Error (_, msg), _ | _, _, _, Error (_, msg) -> 
                Error ((Lam (x, e), Lam (x', e')), "Failed endpoint unification of\n  " ^ Pretty.printf e ^ 
                  "[" ^ x ^ "/i0]\nwith\n  " ^ Pretty.printf e' ^ "[" ^ x' ^ "/i0]\nand\n  " ^ Pretty.printf e ^ 
                  "[" ^ x ^ "/i1]\nwith\n  " ^ Pretty.printf e' ^ "[" ^ x' ^ "/i1]\n" ^ msg)
              end
            | Error (_, msg), _ | _, Error (_, msg) -> (* This case is impossible *)
              Error ((Lam (x, e), Lam (x', e')), msg)
            end
          | _ ->
            let v1 = Expr.init_fresh vars in
            let ev1 = Expr.open_var 0 (Global v1) e in
            let ev1' = Expr.open_var 0 (Global v1) e' in
            let tyv1 = Expr.open_var 0 (Global v1) ty2 in
            let u = unify global ind_env ((v1, ty1, true) :: ctx) lvl sl ph (vars+1) (ev1, ev1', tyv1) lift in
            begin match u with
            | Ok s -> Ok (Lam (v1, s))
            | Error msg -> Error msg
            end
          end

      | App (e1, e2), App (e1', e2'), ty ->
        let h1 = Placeholder.generate ph [] in
        let elab2 = elaborate global ind_env ctx lvl sl h1 (ph+1) vars e2 in
        begin match elab2 with
        | Ok (_, ty2, _) ->
          let u2 = unify global ind_env ctx lvl sl (ph+1) vars (e2, e2', ty2) lift in
          let v1 = Expr.init_fresh vars in
          let u1 = unify global ind_env ctx lvl sl (ph+1) (vars+1) (e1, e1', Pi(v1, ty2, Expr.fullsubst 0 e2 (Local 0) true ty)) lift in
          begin match u1, u2 with
          | Ok s1, Ok s2 -> Ok (App (s1, s2))
          | Error (ex, msg), _ | _, Error (ex, msg) -> 
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
              let ui0 = unify global ind_env ctx lvl sl (ph+1) (vars+1) (i0 e1, i0 e1', ty2) lift in
              let ui1 = unify global ind_env ctx lvl sl (ph+1) (vars+1) (i1 e1, i1 e1', ty2) lift in
              helper ui0 ui1
            
            | _, Global _, Int() ->
              let i0 x = eval ind_env (App (x, I0())) in
              let i1 x = eval ind_env (App (x, I1())) in
              let ui0 = unify global ind_env ctx lvl sl (ph+1) (vars+1) (App (e1, e2), i0 e1', ty2) lift in
              let ui1 = unify global ind_env ctx lvl sl (ph+1) (vars+1) (App (e1, e2), i1 e1', ty2) lift in
              helper ui0 ui1
            
            | Global _, _, Int() ->
              let i0 x = eval ind_env (App (x, I0())) in
              let i1 x = eval ind_env (App (x, I1())) in
              let ui0 = unify global ind_env ctx lvl sl (ph+1) (vars+1) (i0 e1, App (e1', e2'), ty2) lift in
              let ui1 = unify global ind_env ctx lvl sl (ph+1) (vars+1) (i1 e1, App (e1', e2'), ty2) lift in
              helper ui0 ui1

            | _ ->
              (* Try again now by evaluating both applications *)
              let app1 = App (e1, e2) in
              let app2 = App (e1', e2') in
              (* TODO: this is not ideal, to avoid re-evaluation, better store values in a hasthtable and look them up *)
              let app1' = eval ind_env app1 in
              let app2' = eval ind_env app2 in
              if app1 = app1' && app2 = app2' then
              Error (ex, "Failed to unify the applications " ^ Pretty.printf (App (e1, e2)) ^ 
              " and " ^ Pretty.printf (App (e1', e2')) ^ ". " ^ msg)
              else
                unify global ind_env ctx lvl sl (ph+1) (vars+1) (app1', app2', ty) lift
            end
          end
        | Error (_, msg) -> (* This case is impossible *)
          Error ((App (e1, e2), App (e1', e2')), 
          "Failed to check that " ^ Pretty.printf e2 ^ " has type " ^ Pretty.printf h1 ^ "\n" ^ msg)
        end
      
      | App (e, i), e', _ | e', App (e, i), _ ->
          let h1 = Placeholder.generate ph [] in
          let elab2 = elaborate global ind_env ctx lvl sl h1 (ph+1) vars i in
          begin match elab2, i with
          | Ok (_, Int(), _), Global _ ->
            let e0 = eval ind_env (App (e, I0())) in
            let e1 = eval ind_env (App (e, I1())) in
            let e0' = eval ind_env (Expr.fullsubst 0 i (I0()) true e') in
            let e1' = eval ind_env (Expr.fullsubst 0 i (I1()) true e') in
            let ui0 = unify global ind_env ctx lvl sl (ph+1) vars (e0, e0', ty) lift in
            let ui1 = unify global ind_env ctx lvl sl (ph+1) vars (e1, e1', ty) lift in
            begin match ui0, ui1 with
            | Ok _, Ok _ -> Ok (App (e, i))
            | Error msg, _ -> 
              Error ((e0, e0'), "Don't know how to unify the application i0-endpoint\n  " ^ Pretty.printf e0 ^ "\nwith\n  " ^ Pretty.printf e0' ^ "\n" ^ Pretty.printf (eval ind_env e0') ^ "\n" ^ snd msg )
            | _, Error msg -> Error ((e1, e1'), "Don't know how to unify the application i1-endpoint\n  " ^ Pretty.printf e1 ^ "\nwith\n  " ^ Pretty.printf e1' ^ "\n" ^ snd msg)
            end
          | _ ->
            Error ((e, e'), "Don't know how to unify the applied term\n  " ^ Pretty.printf (App (e, i)) ^ "\nwith\n  " ^ Pretty.printf e')
            (* Fallback case: try again after evaluating the second argument *)
            (* let i = eval ind_env i in
            let app = eval ind_env (App (e, i)) in
            if app = App(e, i) then (* TODO: optimize reevaluation with hash consing *)
              Error ((e, e'), "Don't know how to unify the applied term\n  " ^ Pretty.printf (App (e, i)) ^ "\nwith\n  " ^ Pretty.printf e')
            else
              unify global ind_env ctx lvl sl ph vars (app, e', ty) lift *)
          end
      
      | Pair (e1, e2), Pair (e1', e2'), Sigma(_, ty1, ty2) ->
        let u1 = unify global ind_env ctx lvl sl ph vars (e1, e1', ty1) lift in
        let u2 = unify global ind_env ctx lvl sl ph vars (e2, e2', Expr.open_var 0 (Fst e1) ty2) lift in
        begin match u1, u2 with
        | Ok s1, Ok s2 -> Ok (Pair (s1, s2))
        | Error msg, _ | _, Error msg -> Error msg
        end
      
      | Coe (i, j, e1, e2) , Coe (i', j', e1', e2'), _ ->
        let ui = unify global ind_env ctx lvl sl ph vars (i, i', Int()) lift in
        let uj = unify global ind_env ctx lvl sl ph vars (j, j', Int()) lift in
        let h0 = Placeholder.generate ph [] in
        let elab = elaborate global ind_env ctx lvl sl h0 (ph+1) vars e1 in
        begin match elab with
        | Ok (_, eTy, _) ->
          let u1 = unify global ind_env ctx lvl sl (ph+1) vars (e1, e1', eTy) lift in
          let e2 = eval ind_env e2 and e2' = eval ind_env e2' in
          let u2 = unify global ind_env ctx lvl sl (ph+1) vars (e2, e2', eval ind_env (App(e1', i'))) lift in
          begin match ui, uj, u1, u2 with
          | Ok si, Ok sj, Ok s1, Ok s2 -> Ok (Coe (si, sj, s1, s2))
          | Error msg, _, _, _ | _ , Error msg, _, _ | _ , _, Error msg, _ | _ , _, _, Error msg -> 
            Error msg
          end
        | Error (_, msg) -> 
          Error ((Coe (i, j, e1, e2) , Coe (i', j', e1', e2')), msg)
        end
      
      | Hcom (i, j, e, e1, e2) , Hcom (i', j', e', e1', e2'), _ ->
        let h0 = Placeholder.generate ph [] in
        let elab = elaborate global ind_env ctx lvl sl h0 (ph+1) vars e in
        (* Syntactic equality as interval variables are expected to be atoms *)
        if i = i' && j = j' then
          begin match elab with
          | Ok (_, eTy, _) ->
            let u = unify global ind_env ctx lvl sl (ph+1) vars (e, e', eTy) lift in
            let u1 = unify global ind_env ctx lvl sl (ph+1) vars (e1, e1', eTy) lift in
            let u2 = unify global ind_env ctx lvl sl (ph+1) vars (e2, e2', eTy) lift in
            begin match u, u1, u2 with
            | Ok se, Ok se1, Ok se2 -> Ok (Hcom (i, j, se, se1, se2))
            | Error msg, _, _ | _ , Error msg, _ | _ , _, Error msg -> 
              Error msg
            end
          | Error (_, msg) -> 
            Error ((Hcom (i, j, e, e1, e2) , Hcom (i', j', e', e1', e2')), msg)
          end
        else
          Error ((Hcom (i, j, e, e1, e2) , Hcom (i', j', e', e1', e2')), 
          "Cannot unify " ^ Pretty.printf i ^ " with " ^ Pretty.printf i' ^ " or " ^ Pretty.printf j ^ " with " ^ Pretty.printf j')

      | At (Hole _, Hole _), e', _ | e', At (Hole _, Hole _), _ ->
        Ok e'
      
      | At (e1, e2), At (e1', e2'), ty ->
        let u2 = unify global ind_env ctx lvl sl ph vars (e2, e2', Int()) lift in
        let h1 = Placeholder.generate ph [] in
        let h2 = Placeholder.generate (ph+1) [] in
        let v1 = Expr.init_fresh vars in
        let elab1 = elaborate global ind_env ctx lvl sl (Pathd (Pi(v1, Int(), Expr.fullsubst 0 e2 (Local 0) true ty), h1, h2)) (ph+2) (vars+1) e1 in
        begin match elab1 with
        | Ok (_, ety, _) ->
          let u1 = unify global ind_env ctx lvl sl (ph+2) (vars+1) (e1, e1', ety) lift in
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
          let elab = elaborate global ind_env ctx lvl sl ty ph vars (At (e, i)) in
          begin match elab with
          | Ok (ei, ety, _) ->
            let u1 = unify global ind_env ctx lvl sl ph vars (ei, e', ety) lift in
            begin match u1 with
            | Ok se -> Ok se
            | Error msg -> Error msg
            end
          | Error (_, msg) ->
            Error ((At (e, i), e'), msg)
          end
        
        (* Otherwise elaborate and unify e @ ε with e' [ε/i] : ty [ε/i] *)
        else
          let h1 = Placeholder.generate ph [] in
          begin match i with
          | Global x ->
            (* Infer the endpoints of the type line *)
            let elabt0 = elaborate global ind_env ctx lvl sl h1 (ph+1) vars (eval ind_env (Global.subst_global 0 (I0()) x ty)) in
            let elabt1 = elaborate global ind_env ctx lvl sl h1 (ph+1) vars (eval ind_env (Global.subst_global 0 (I1()) x ty)) in
            begin match elabt0, elabt1 with
            | Ok (ty0, _, _), Ok (ty1, _, _) ->
              (* Check that the endpoints of e inhabit the type line endpoints *)
              let elab0 = elaborate global ind_env ctx lvl sl ty0 (ph+1) vars (At (eval ind_env (Global.subst_global 0 (I0()) x e), I0())) in
              let elab1 = elaborate global ind_env ctx lvl sl ty1 (ph+1) vars (At (eval ind_env (Global.subst_global 0 (I1()) x e), I1())) in
              (* Check that the endpoints of e' inhabit the type line endpoints *)
              let elab0' = elaborate global ind_env ctx lvl sl ty0 (ph+1) vars (eval ind_env (Global.subst_global 0 (I0()) x e')) in
              let elab1' = elaborate global ind_env ctx lvl sl ty1 (ph+1) vars (eval ind_env (Global.subst_global 0 (I1()) x e')) in
              begin match elab0, elab1, elab0', elab1' with
              | Ok (e0, _, _), Ok (e1, _, _), Ok (e0', _, _), Ok (e1', _, _) ->
                (* Unify the corresponding endpoints of e and e' *)
                let ui0 = unify global ind_env ctx lvl sl (ph+1) vars (e0, e0', ty0) lift in
                let ui1 = unify global ind_env ctx lvl sl (ph+1) vars (e1, e1', ty1) lift in
                begin match ui0, ui1 with
                | Ok _, Ok _ -> Ok (App (e, i))
                | Error msg, _ -> 
                  Error ((e0, e0'), "Don't know how to unify\n  " ^ Pretty.printf e0 ^ "\nwith\n  " ^ Pretty.printf e0' ^ "\n" ^ Pretty.printf (eval ind_env e0') ^ "\n" ^ snd msg ) 
                | _, Error msg -> 
                  Error ((e1, e1'), "Don't know how to unify\n  " ^ Pretty.printf e1 ^ "\nwith\n  " ^ Pretty.printf e1' ^ "\n" ^ snd msg)
                end
              | Error (_, msg), _, _, _ | _, Error (_, msg), _, _ | _, _, Error (_, msg), _ |  _, _, _, Error (_, msg) ->
                Error ((At (e, i), e'), msg)
              end

            | Error (_, msg), _ | _, Error (_, msg) -> 
              Error ((At (e, i), e'), msg) (* This case is impossible *)
            end
          | _ ->
            Error ((e, e'), "Don't know how to unify\n  " ^ Pretty.printf (App (e, i)) ^ "\nwith\n  " ^ Pretty.printf e')
          end
            
      | Fst e, Fst e', ty ->
        let v1 = Expr.init_fresh vars in
        let h1 = Placeholder.generate ph [] in
        let elab = elaborate global ind_env ctx lvl sl (Sigma(v1, ty, h1)) (ph+1) (vars+1) e in
        begin match elab with
        | Ok (_, ety, _) ->
          let u = unify global ind_env ctx lvl sl (ph+1) (vars+1) (e, e', ety) lift in
          begin match u with
          | Ok s -> Ok (Fst s)
          | Error msg -> Error msg
          end
        | Error (_, msg) -> (* This case is impossible *)
          Error ((Fst e, Fst e'), msg)
        end

      | Snd e, Snd e', ty ->
        let v1 = Expr.init_fresh vars in
        let h1 = Placeholder.generate ph [] in
        let elab = elaborate global ind_env ctx lvl sl (Sigma(v1, h1, Expr.fullsubst 0 (Fst e) (Local 0) true ty)) (ph+1) (vars+1) e in
        begin match elab with
        | Ok (_, ety, _) ->
          let u = unify global ind_env ctx lvl sl (ph+1) (vars+1) (e, e', ety) lift in
          begin match u with
          | Ok s -> Ok (Snd s)
          | Error msg -> Error msg
          end
        | Error (_, msg) -> (* This case is impossible *)
          Error ((Snd e, Snd e'), msg)
        end

      | Abort e, Abort e', _ ->
        let u = unify global ind_env ctx lvl sl ph vars (e, e', Void()) lift in
        begin match u with
        | Ok s -> Ok (Abort s)
        | Error msg -> Error msg
        end

      | Type m, Type n, _ ->
        (* Helper compare function *)
        let compare m n = if lift then if Level.leq n m then Ok (Type n) else
            Error ((Type m, Type n), "Could not unify after lifting the universe levels of the types\n  " ^ Pretty.printf (Type m) ^ "\nand\n  " ^ Pretty.printf (Type n))
          else
            Error ((Type m, Type n), "The types\n  " ^ Pretty.printf (Type m) ^ "\nand\n  " ^ Pretty.printf (Type n) ^ "\nhave incompatible universe levels")
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
          Error ((Lam (x, e), e'), "Don't know how to unify the abstraction\n  " ^ Pretty.printf (Lam (x, e)) ^ "\nwith the term\n  " ^ Pretty.printf e')
        else
          unify global ind_env ctx lvl sl ph vars (abs, e', ty) lift
      
      | Pair (e1, e2) , e', _ | e', Pair (e1, e2), _ ->
        let e1 = eval ind_env e1 and e2 = eval ind_env e2 in
        let pair = eval ind_env (Pair (e1, e2)) in (* for any possible eta reduction *)
        (* Needs to be optimized to avoid reevaluation *)
        if Pair (e1, e2) = pair && not (e' = pair) then
          Error ((Pair (e1, e2), e'), "Don't know how to unify the pair\n  " ^ Pretty.printf (Pair (e1, e2)) ^ "\nwith the term\n  " ^ Pretty.printf e')
        else
          unify global ind_env ctx lvl sl ph vars (pair, e', ty) lift
      
      | Pabs (i, e) , e', _ | e', Pabs (i, e), _ ->
        let e1 = eval ind_env e in
        let pabs = eval ind_env (Pabs (i, e1)) in (* for any possible eta reduction *)
        (* Needs to be optimized to avoid reevaluation *)
        if Pabs (i, e) = pabs && not (e' = pabs) then
          Error ((Pabs (i, e), e'), "Don't know how to unify the abstraction\n  " ^ Pretty.printf (Pabs (i, e)) ^ "\nwith the term\n  " ^ Pretty.printf e')
        else
          unify global ind_env ctx lvl sl ph vars (pabs, e', ty) lift

      | e , e', _ -> 
        if eval ind_env e = eval ind_env e' then 
          Ok e 
        else 
          Error ((e, e'), "The two terms\n  " ^ Pretty.printf e ^ "\nand\n  " ^ Pretty.printf e' ^ "\nare not equal")