{
(**
  (c) Copyright 2019 Bruno Bentzen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Desc: Performs the lexical analysis of the program. The lexer supports 
        some unicode characters, recognizes identifiers, numbers, and 
        keywords, and ignores whitespace and comments.
 **)

open Syntax
}

let identifier =
  ['A'-'Z' 'a'-'z']['A'-'Z' 'a'-'z' '0'-'9' '_' ''']* as str

let idlistcolon =
  ['A'-'Z' 'a'-'z']['A'-'Z' 'a'-'z' '0'-'9' '_' ''']*
  ([' ' '\t']+ ['A'-'Z' 'a'-'z']['A'-'Z' 'a'-'z' '0'-'9' '_' ''']*)*
  [' ' '\t']* ':' [' ' '\t']+ as str

let filename =
  ['.']['.']? '/' ['A'-'Z' '.' 'a'-'z' '0'-'9' '_' '.' '/']* as str
| ['A'-'Z' 'a'-'z']['A'-'Z' 'a'-'z' '0'-'9' '_' '.']* as str

let number =
  ['0'-'9']* as str

let whitespace =
  [' ' '\t']+

let end_of_line =
    '\r'
  | '\n'
  | "\r\n"

rule token = parse
  | "/*"               { comment lexbuf } (* Comments *)
  | "i0"               { I0 }
  | "i1"               { I1 }
  | "I"                { INTERVAL }
  | "𝕀"                { INTERVAL }
  | "coe"              { COE }
  | "com"              { COM }
  | "hcom"             { HCOM }
  | "|"                { BAR }
  | "⁻¹"               { SYMM }
  | "·"                { TRANS }
  | "λ"                { ABS }
  | "app"              { APP }
  | "->"               { RARROW }
  | "→"                { RARROW }
  | "↔"                { LRARROW }
  | "Π"                { PI }
  | "∏"                { PI }
  | "("                { LPAREN }
  | ","                { COMMA }
  | ")"                { RPAREN }
  | "×"                { PROD }
  | "⨉"                { PROD }
  | "Σ"                { SIGMA }
  | "+"                { SUM }  
  | "0"                { ZERO }
  | "ℕ"                { NAT }
  | "()"               { STAR }
  | "abort"            { ABORT }
  | "empty"            { VOID }
  | "void"             { VOID }
  | "¬"                { NEG }
  | "<"                { LANGLE }
  | ">"                { RANGLE }
  | "@"                { AT }
  | "refl"             { REFL }
  | "path"             { PATH }
  | "pathd"            { PATHD }
  | "_"                { WILDCARD }
  | "??"               { PLACEHOLDER }
  | "?"                { SUBGOAL }
  | ":="               { COLONEQ }
  | "type"             { TYPE }
  | "max"              { MAX }
  | "next"             { NEXT }
  | ":"                { COLON }
  | "{"                { LBRACE }
  | "}"                { RBRACE }
  | "import"           { IMPORT }
  | "inductive"        { IND }
  | "open"             { IMPORT }
  | "universe"         { UNIVERSE }
  | "definition"       { DEF }
  | "def"              { DEF }
  | "lemma"            { DEF }
  | "lem"              { DEF }
  | "theorem"          { DEF }
  | "thm"              { DEF }
  | "print"            { PRINT }
  | "infer"            { INFER }
  | "eval"             { EVAL }
  | whitespace         { token lexbuf }
  | end_of_line        { Lexing.new_line lexbuf; token lexbuf } 
  | identifier         { ID(str) }
  | filename           { FILENAME(str) }
  | number             { NUMBER(str) }
  | _ as chr           { failwith ("Lexer does not recognize the token '"^(Char.escaped chr)^"'") }
  | eof                { EOF }

and comment = parse
  | "*/"               { token lexbuf }
  | _                  { comment lexbuf }
