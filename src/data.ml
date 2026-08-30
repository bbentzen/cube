(**
  (c) Copyright 2026 Bruno Bentzen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Desc: Stores information about inductive types and their constructors, including 
        the number of parameters, indices, and recursive arguments. This information 
        is used for type checking and elaboration of inductive types in the type system.
        This file also governs other hash tables used for hash consing.
 **)


(* Hash tables for generating and evaluating recursors *)

type constr_spec = {
  c_name : string;
  c_num_args : int;
  c_rec_args : bool list; (* true for recursive arguments requiring IH *)
}

type ind_spec = {
  ind_name : string;
  num_indices : int;
  num_params : int;
  constructors : constr_spec list;
}

(* Hash table for inferring constructor type information *)

type con_spec = {
  ind_name : string;
  num_indices : int;
  num_params : int;
}