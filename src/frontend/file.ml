(**
  (c) Copyright 2019 Bruno Bentzen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Desc: Performs basic file operations, including reading files, parsing strings and files, and handling directories. 
        It also provides functions for resolving import paths relative to the current file.
 **)

open Basis

type command_location = {
  line : int;
  col_start : int;
  col_end : int;
}

let current_location lb =
  let startp = Lexing.lexeme_start_p lb in
  let endp = Lexing.lexeme_end_p lb in
  {
    line = startp.pos_lnum;
    col_start = startp.pos_cnum - startp.pos_bol;
    col_end = endp.pos_cnum - endp.pos_bol;
  }

let read_file filename = 
  let lines = ref [] in
  let chan = open_in filename in
  try
    while true; do
      lines := input_line chan :: !lines
    done; !lines
  with End_of_file ->
    close_in chan;
    List.rev !lines ;;

let rec concat_string_list = function
  | [] -> ""
  | [s] -> s
  | s :: l -> s ^ "\n" ^ concat_string_list l

(* Parses a string *)

let parse_string s =
  let lb = Lexing.from_string s in
  try
    Syntax.command Scanner.token lb
  with
  | exn ->
      let exn_name = Printexc.to_string exn in
      if exn_name = "Basis.Syntax.MenhirBasics.Error" || exn_name = "Syntax.MenhirBasics.Error" then
        let startp = Lexing.lexeme_start_p lb in
        let endp = Lexing.lexeme_end_p lb in
        let line = startp.pos_lnum in
        let col_start = startp.pos_cnum - startp.pos_bol in
        let col_end = endp.pos_cnum - endp.pos_bol in
        let token_err =
          let lexeme = Lexing.lexeme lb in
          if lexeme = "" then "<EOF>" else lexeme
        in
        failwith
          (Printf.sprintf
             "Line %d, characters %d-%d:\nUnexpected token variant '%s'"
             line col_start col_end token_err)
      else
        raise exn

let token_list_of_string s =
  let lb = Lexing.from_string s in
  let rec helper l =
    try
      let t = Scanner.token lb in
      if t = Syntax.EOF then List.rev l else helper (t::l)
    with _ -> List.rev l in 
  helper []

let command_locations_of_string s =
  let lb = Lexing.from_string s in
  let rec helper locations =
    try
      let token = Scanner.token lb in
      let locations' =
        match token with
        | Syntax.DEF
        | Syntax.PRINT
        | Syntax.INFER
        | Syntax.IMPORT
        | Syntax.UNIVERSE -> current_location lb :: locations
        | _ -> locations
      in
      if token = Syntax.EOF then List.rev locations'
      else helper locations'
    with _ ->
      List.rev locations
  in
  helper []

let command_locations_of_file filename =
  command_locations_of_string (concat_string_list (read_file filename))
  
let parse_file filename = 
  parse_string (concat_string_list (read_file filename))

(* Handles directories *)

let parent dir =
  if dir = "" then "."
  else Filename.dirname dir

let normalize_path path =
  let parts = String.split_on_char '/' path in
  let rec loop acc = function
    | [] -> List.rev acc
    | "." :: rest -> loop acc rest
    | ".." :: rest ->
        begin
          match acc with
          | [] -> loop [".."] rest
          | _ :: rest_acc -> loop rest_acc rest
        end
    | part :: rest -> loop (part :: acc) rest
  in
  let normalized = loop [] parts in
  match normalized with
  | [] -> "."
  | parts -> String.concat "/" parts

let resolve_path current_file import_path =
  let candidate =
    if Filename.is_relative import_path then
      let parent_dir = parent current_file in
      if parent_dir = "." then import_path
      else Filename.concat parent_dir import_path
    else
      import_path
  in
  normalize_path candidate