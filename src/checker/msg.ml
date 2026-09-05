(**
  (c) Copyright 2019 Bruno Bentzen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Desc: This module contains error messages displayed by the type checker and elaborator.
 **)

open Basis

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