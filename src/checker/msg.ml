(**
  (c) Copyright 2019 Bruno Bentzen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Desc: This module contains error messages displayed by the type checker and elaborator.
 **)

open Basis
open Context

(* Locals *)

let unexpected index ty ctx =
  "Unexpected local variable when checking that the term " ^
  Pretty.printf (Local index) ^
  " has type " ^ Pretty.printf ty ^
  "\n" ^ Global.printf ctx

(* Globals *)

let goal_msg ctx e ty =
  "when checking that\n  " ^ Pretty.printf e ^ "\nhas the expected type\n" ^ Global.printf ctx ^ 
  "-------------------------------------------\n ⊢ " ^ Pretty.printf ty

let undeclared x =
  "No declaration for the variable " ^ x

let var_type_mismatch x xty ty msg = 
  "The variable " ^ x ^ " has type\n   " ^ Pretty.printf xty ^ 
  "\nbut is expected to have type\n  " ^ Pretty.printf ty ^ "\n" ^ msg

let var_error x msg = 
  "Error at type checking the variable " ^ x ^ ": " ^ msg

let var_type_mismatch_2 x xty ty = 
  "The variable " ^ x ^ " has type\n   " ^ Pretty.printf xty ^ 
  "\nbut is expected to have type\n  " ^ Pretty.printf ty ^ "\n"

(* Intervals *)

let i0_error ty =
  "Type mismatch when checking that the endpoint 
  i0 of type I has type " ^ Pretty.printf ty

let i1_error ty =
  "Type mismatch when checking that the endpoint 
  i1 of type I has type " ^ Pretty.printf ty

(* Functions *)

let lam_error x e ty =
  "The term\n  " ^ Pretty.printf (Lam (x, e)) ^ 
  "\nhas type\n  " ^ Pretty.printf ty ^ "\nbut is expected to have type\n  Π (v? : ?0?) ?1?"

let app_fail_1 e2' ty1' msg = 
  "Failed application: the term in the argument position \n  " ^ Pretty.printf e2' ^ 
  "\nis expected to have type\n  " ^ Pretty.printf ty1' ^ "\n" ^ msg

let app_fail_2 e2 ty1' msg = 
  "Failed application: the term in the argument\n  " ^ Pretty.printf e2 ^ 
  "\nis expected to have type\n  " ^ Pretty.printf ty1' ^ "\n" ^ msg

let app_wrong_ty1 e1' h2 ty1' =
  "Failed application: the term in function position\n  " ^ Pretty.printf e1' ^ 
  "\nis expected to have the type\n " ^ Pretty.printf h2 ^
  "\nbut was found to have type\n " ^ Pretty.printf ty1'

let app_wrong_ty2 e1 msg =
  "Failed application: the term in function position\n  " ^ Pretty.printf e1 ^ 
  "\nis expected to have a function type.\n " ^ msg

(* Void *)

let void_error e msg =
  "Type mismatch when checking that " ^ Pretty.printf e ^ 
  "has type " ^ Pretty.printf (Void()) ^ ". " ^ msg

(* Coercion *)

let coercion_error_1 tyj ty' eTy i j ety e ty msg =
  "Failed to unify the terms\n  " ^ Pretty.printf tyj ^ "\nand\n  " ^ Pretty.printf ty' ^ 
  "\nof expected type\n  " ^ Pretty.printf eTy ^
  "\nwhen checking that the coercion\n  " ^ Pretty.printf (Coe(i, j, ety, e)) ^
  "\nhas type\n  " ^ Pretty.printf ty ^
  "\n" ^ msg

let coercion_error_2 e tyi msg =
  "The coercion failed because\n  " ^ Pretty.printf e ^
  "\ndoes not have type\n  " ^ Pretty.printf tyi ^ "\n" ^ msg

let coercion_error_3 ty msg =
  "Error at the coercion stage when checking that" ^ Pretty.printf ty ^ " is a type: " ^ msg

let coercion_error_i i msg =
  "Error at the coercion stage: " ^ Pretty.printf i ^ " must have type I. " ^ msg

let coercion_error_ty tyi_expr i msg =
"Failed while elaborating coercion family instance " ^ Pretty.printf tyi_expr ^ " at " ^ Pretty.printf i ^ "\n" ^ msg

(* Homogeneous composition *)

let lid_unify ind_env ei0 i1 e1i0 msg =
  "Invalid composition scenario: Error when unifying the i0-endpoint of the lid \n  " ^ 
  Pretty.printf (Eval.eval ind_env ei0) ^ "\nwith the " ^ Pretty.printf i1 ^ 
  "-endpoint of the i0-tube \n  " ^ Pretty.printf (Eval.eval ind_env e1i0) ^ "\n" ^ msg

let tube_i1_unify ind_env ei1 i1 e2i0 msg =
  "Invalid composition scenario: Error when unifying the terms\n  " ^ 
  Pretty.printf (Eval.eval ind_env ei1) ^ "\nwith the " ^ Pretty.printf i1 ^ 
  "-endpoint of the i1-tube \n  " ^ Pretty.printf (Eval.eval ind_env e2i0) ^ "\n" ^ msg

let lid_i0 ind_env i1 j1 e' e1' e2' ty' msg =
  "Error when checking that the homogeneous composition  " ^ Pretty.printf (Hcom(i1, j1, e', e1', e2')) ^ 
  "\nhas type\n  I → " ^ Pretty.printf ty' ^ "\nThe i0-face of the lid\n  " ^ 
  Pretty.printf (Eval.eval ind_env (App(e', I0()))) ^ "\ndoes not have the expected type\n  " ^ 
  Pretty.printf ty' ^ "\n" ^ msg

let lid_i1 ind_env i1 j1 e' e1' e2' ty' msg =
  "Error when checking that the homogeneous composition\n  " ^ Pretty.printf (Hcom(i1, j1, e', e1', e2')) ^ 
  "\nhas type\n  I → " ^ Pretty.printf ty' ^ "\nThe i1-face of the lid\n  " ^ 
  Pretty.printf (Eval.eval ind_env (App(e', I1()))) ^ "\ndoes not have the expected type\n  " ^ 
  Pretty.printf ty' ^ "\n" ^ msg

let tube_i0 ind_env i1 j1 e' e1' e2' ty' msg =
  "Error when checking that the homogeneous composition\n  " ^ Pretty.printf (Hcom(i1, j1, e', e1', e2')) ^ 
  "\nhas type\n  I → " ^ Pretty.printf ty' ^ "\nThe i0-face of the i0-tube\n  " ^ 
  Pretty.printf (Eval.eval ind_env (App(e1', I0()))) ^ "\ndoes not have the expected type\n  " ^ 
  Pretty.printf ty' ^ "\n" ^ msg

let tube_i1 ind_env i1 j1 e' e1' e2' ty' msg =
  "Error when checking that the homogeneous composition\n  " ^ Pretty.printf (Hcom(i1, j1, e', e1', e2')) ^ 
  "\nhas type\n  I → " ^ Pretty.printf ty' ^ "\nThe i0-face of the i1-tube\n  " ^ 
  Pretty.printf (Eval.eval ind_env (App(e2', I0()))) ^ "\ndoes not have the expected type\n  " ^ 
  Pretty.printf ty' ^ "\n" ^ msg

let hcom_error msg =
  "Failed to typecheck the lid or tubes of the homogeneous composition: " ^ msg

let tube_i0_meta ind_env i1 j1 e' e1' e2' ty0 msg =
  "Error when synthesizing type for the homogeneous composition\n  " ^ 
  Pretty.printf (Hcom(i1, j1, e', e1', e2')) ^ "\nThe i0-face of the i0-tube\n  " ^ 
  Pretty.printf (Eval.eval ind_env (App(e1', I0()))) ^ "\ndoes not have the expected type\n  " ^ 
  Pretty.printf ty0 ^ "\n" ^ msg

let tube_i1_meta ind_env i1 j1 e' e1' e2' ty0 msg =
  "Error when synthesizing type for the homogeneous composition\n  " ^ 
  Pretty.printf (Hcom(i1, j1, e', e1', e2')) ^ "\nThe i0-face of the i1-tube\n  " ^ 
  Pretty.printf (Eval.eval ind_env (App(e1', I0()))) ^ "\ndoes not have the expected type\n  " ^ 
  Pretty.printf ty0 ^ "\n" ^ msg

let lid_meta ind_env e' ety e1' e2' ty' msg =
  "Failed to synthesize placeholder type. The lid " ^ Pretty.printf e' ^ " has type " ^ 
  Pretty.printf ety ^ ", but could not check that the line\n  " ^ 
  Pretty.printf (Eval.eval ind_env (App(e', I1()))) ^ "\nhas type\n  " ^ 
  Pretty.printf ty' ^ "\nin the homogeneous composition\n  
  hfill (" ^ Pretty.printf e' ^ ")\n    | i0 → " ^ Pretty.printf e1' ^
  "\n    | i1 → " ^ Pretty.printf e2' ^ "\n" ^ msg

let lid_unexpected e ety =
  "The lid of the homogeneous composition\n  " ^ Pretty.printf e ^ 
  "\nis expected to have the function type but has type\n  " ^ Pretty.printf ety

let hcom_unexpected_1 i1 j1 e e1 e2 k int ty' =
  "The homogeneous composition " ^ Pretty.printf (Hcom(i1, j1, e, e1, e2)) ^ 
  "\nhas type\n  " ^ Pretty.printf (Pi(k, int, ty')) ^
  "\nbut is expected to have type\n  I → ?0?"

let hcom_unexpected_2 i1 j1 e e1 e2 ty =
  "The homogeneous composition\n  " ^ 
  Pretty.printf (Hcom(i1, j1, e, e1, e2)) ^ 
  "\nis expected to have type\n  I → ?0?\nand not\n  " ^ 
  Pretty.printf ty

(* Paths *)

let pabs_unify msg =
  "Type unification error in path abstraction.\n" ^ msg

let pabs_error msg =
  "Typehood error in path abstraction.\n" ^ msg

let pabs_unify_i0 i e1 ei0 e e' ty ctx =
  "Error in path abstraction over " ^ i ^ ": I. Failed to unify\n  " ^
  Pretty.printf e1 ^ "\nwith\n  " ^ Pretty.printf ei0 ^ "≡ " ^ Pretty.printf e ^ "[i0/" ^ i ^ "]" ^ "\n" ^
  goal_msg ctx (Pabs (i, e')) ty

let pabs_unify_i1 i e2 ei1 e e' ty ctx =
  "Failed to unify\n  " ^ Pretty.printf e2 ^ "\nwith\n  " ^ 
  Pretty.printf ei1 ^ "≡ " ^ Pretty.printf e ^ "[i1/" ^ i ^ "]" ^ "\n" ^
  goal_msg ctx (Pabs (i, e')) ty

let pabs_syn msg =
  "Failed synthetization of type placeholder for i0-endpoint in path abstraction.\n" ^ msg

let pabs_unify_i0_2 v1 e1 ei0 e' ty ctx msg =
  "Error in path abstraction over " ^ v1 ^ " : I when attempting unification at the i0-endpoint. Failed to unify\n  " ^
  Pretty.printf e1 ^ "\nwith\n  " ^ Pretty.printf ei0 ^ "≡ " ^ Pretty.printf e' ^ "[i0/" ^ v1 ^ "]" ^ "\n" ^
  msg ^ "\n" ^ goal_msg ctx (Pabs (v1, e')) ty 

let pabs_unify_i0_3 v1 e1 ei0 e' ty ctx msg =
  "Failed to unify\n  " ^ 
  Pretty.printf e1 ^ "\nwith\n  " ^ Pretty.printf ei0 ^ "≡ " ^ Pretty.printf e' ^ "[i0/" ^ v1 ^ "]" ^ "\n" ^
  msg ^ "\n" ^ goal_msg ctx (Pabs (v1, e')) ty

let pabs_unify_i1_2 v1 e2 ei1 e' ty ctx msg =
  "Error in path abstraction over " ^ v1 ^ " : I when attempting unification at the i1-endpoint. Failed to unify\n  " ^ 
  Pretty.printf e2 ^ "\nwith\n  " ^ Pretty.printf ei1 ^ "≡ " ^ Pretty.printf e' ^ "[i1/" ^ v1 ^ "]" ^ "\n" ^
  msg ^ "\n" ^ goal_msg ctx (Pabs (v1, e')) ty

let pabs_unify_i1_3 v1 e2 ei1 e' ty ctx msg =
  "Failed to unify\n  " ^ 
  Pretty.printf e2 ^ "\nwith\n  " ^ Pretty.printf ei1 ^ "≡ " ^ Pretty.printf e' ^ "[i1/" ^ v1 ^ "]" ^ "\n" ^
  msg ^ "\n" ^ goal_msg ctx (Pabs (v1, e')) ty

let pabs_unify_i1_4 v1 e2 e2' ei1 ei1' e' ty ctx msg =
  "Unification error at path abstraction. Failed to unify\n  " ^
  Pretty.printf e2 ^ "\nwith\n  " ^ Pretty.printf ei1 ^ "≡ " ^ Pretty.printf e' ^ "[i1/" ^ v1 ^ "]" ^ 
  "\n" ^  Pretty.printf ei1' ^ "\n" ^  Pretty.printf e2' ^
  "\n" ^ msg ^ "\n" ^ goal_msg ctx (Pabs (v1, e')) ty

let pabs_i0_ty ind_env v1 e ty e' ty1 msg =
  "Error when checking that the path abstracted term\n  " ^ 
  Pretty.printf (Pabs(v1, Eval.eval ind_env e)) ^ "\nhas type\n  " ^ Pretty.printf ty ^ 
  "\nThe i0-endpoint\n  " ^ Pretty.printf (Eval.eval ind_env (Expr.open_var 0 (I0()) e')) ^ 
  "\ndoes not have type\n  " ^ Pretty.printf (Eval.eval ind_env (App(ty1, I0()))) ^
  "\n" ^ msg

let pabs_i1_ty ind_env v1 e ty e' ty1 msg =
  "Error when checking that the path abstracted term\n  " ^ 
  Pretty.printf (Pabs(v1, Eval.eval ind_env e)) ^ "\nhas type\n  " ^ Pretty.printf ty ^ 
  "\nThe i1-endpoint\n  " ^ Pretty.printf (Eval.eval ind_env (Expr.open_var 0 (I1()) e')) ^ 
  "\ndoes not have type\n  " ^ Pretty.printf (Eval.eval ind_env (App(ty1, I1()))) ^ 
  "\n" ^ msg

let pabs_ty_fail ei ty1' msg =
  "Error in the body of path abstraction: failed to check that the body " ^ 
  Pretty.printf ei ^ "\nhas type\n  " ^ Pretty.printf ty1' ^ "\n" ^ msg

let pabs_meta_unify ty' ty'' msg =
  "Failed to unify the types\n  " ^ Pretty.printf ty' ^ "\nand\n  " ^ Pretty.printf ty'' ^ "\n" ^ msg

let pabs_unexpected i e ty ty' = 
  "The expression\n  <" ^ i ^ "> " ^ Pretty.printf e ^ "\nchecked against type " ^ Pretty.printf ty ^ " is expected to have type\n  pathd ?0? ?1? ?2?\nbut has type\n  " ^ Pretty.printf ty'

let pabs_not_ty ind_env ty msg =
  "Failed to prove that\n  " ^ Pretty.printf (Eval.eval ind_env ty) ^ "\nis a type\n" ^ msg

let at_unify ty2' ty =
  "Failed to unify\n  " ^ 
  Pretty.printf ty2' ^ "\nwith\n  " ^ Pretty.printf ty

let path_mismatch e1' ty1' =
  "Type mismatch when checking that\n  " ^ Pretty.printf e1' ^ 
  "\nof type\n  " ^ Pretty.printf ty1' ^ "\nhas type\n  pathd ?0? ?1? ?2? "