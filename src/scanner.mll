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

let greek_lower =
  "α" | "β" | "γ" | "δ" | "ε" | "ζ" | "η" | "θ" | "ι" | "κ" | "μ" | "ν" |
  "ξ" | "ο" | "π" | "ρ" | "σ" | "τ" | "υ" | "φ" | "χ" | "ψ" | "ω"

let greek_upper =
  "Α" | "Β" | "Γ" | "Δ" | "Ε" | "Ζ" | "Η" | "Θ" | "Ι" | "Κ" | "Λ" | "Μ" | "Ν" |
  "Ξ" | "Ο" | "Ρ" | "Τ" | "Υ" | "Φ" | "Χ" | "Ψ" | "Ω"

let mathcal_letter =
  "𝓐" | "𝓑" | "𝓒" | "𝓓" | "𝓔" | "𝓕" | "𝓖" | "𝓗" | "𝓘" | "𝓙" | "𝓚" | "𝓛" | "𝓜" | "𝓝" |
  "𝓞" | "𝓟" | "𝓠" | "𝓡" | "𝓢" | "𝓣" | "𝓤" | "𝓥" | "𝓦" | "𝓧" | "𝓨" | "𝓩" | "ℓ"

let subscript_digit =
  "₀" | "₁" | "₂" | "₃" | "₄" | "₅" | "₆" | "₇" | "₈" | "₉"

let subscript_letter =
  "ₐ" | "ₑ" | "ₕ" | "ᵢ" | "ⱼ" | "ₖ" | "ₗ" | "ₘ" | "ₙ" | "ₚ" | "ₛ" | "ₜ" | "ᵥ" | "ₓ"

let superscript_digit =
  "⁰" | "¹" | "²" | "³" | "⁴" | "⁵" | "⁶" | "⁷" | "⁸" | "⁹"

let superscript_letter =
  "ᵃ" | "ᵇ" | "ᶜ" | "ᵈ" | "ᵉ" | "ᶠ" | "ᵍ" | "ʰ" | "ⁱ" | "ʲ" | "ᵏ" | "ˡ" |
  "ᵐ" | "ⁿ" | "ᵒ" | "ᵖ" | "ʳ" | "ˢ" | "ᵗ" | "ᵘ" | "ᵛ" | "ʷ" | "ˣ" | "ʸ" | "ᶻ"

let ident_start =
  ['A'-'Z' 'a'-'z']
| greek_lower
| greek_upper
| mathcal_letter
| subscript_digit
| subscript_letter
| superscript_digit
| superscript_letter

let ident_continue =
  ident_start
| ['0'-'9' '_']
| "'"

let identifier =
  ident_start ident_continue* as str

let idlistcolon =
  ident_start ident_continue*
  ([' ' '\t']+ ident_start ident_continue*)*
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
  | "abbrev"           { ABBREV }
  | "abbreviation"     { ABBREV }
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
