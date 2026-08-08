%{
(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: The parser of the program
 **)

open Ast

let rec abs_of_list e = function
  | [] -> e
  | id :: l ->
    Ast.Abs(id, abs_of_list e l)

let rec pi_of_list e = function
  | [] -> e
  | (id, ty) :: l ->
    Ast.Pi (id, ty, pi_of_list e l)

let rec sigma_of_list e = function
  | [] -> e
  | (id, ty) :: l ->
    Ast.Sigma (id, ty, sigma_of_list e l)

let rec ids_to_bindings ids ty =
  match ids with
  | [] -> []
  | id :: rest -> (id, ty) :: ids_to_bindings rest ty

let fill_def i j ty e e1 e2 =
  let v1 = Substitution.fresh_var (App(e1, e2)) e 2 in
  Hfill(Abs(v1, Coe (i, j, ty, App(e, Id v1))), 
  Abs(v1, Coe (Id v1, j, ty, App(e1, Id v1))),
  Abs(v1, Coe (Id v1, j, ty, App(e2, Id v1))))

let single_id = function
  | [id] -> id
  | _ -> failwith "Expected exactly one identifier before ':'"

%}

%token <string> ID
%token <string> FILENAME
%token <string> NUMBER
%token EVAL IMPORT IND UNIVERSE DEF PRINT INFER LBRACE RBRACE
%token TYPE MAX NEXT COLON VDASH
%token I0 I1 INTERVAL COE HCOM HFILL FILL COM BAR
%token ABS APP RARROW LRARROW PI
%token LPAREN RPAREN COMMA FST SND PROD SIGMA
%token INL INR CASE SUM
%token ZERO SUCC NATREC NAT
%token TRUE FALSE IF BOOL
%token STAR LET UNIT
%token ABORT VOID NEG
%token LANGLE RANGLE AT REFL SYMM TRANS PATHD PATH
%token WILDCARD PLACEHOLDER COLONEQ SUBGOAL
%token EOF
%right LRARROW
%right PI
%right RARROW
%left AT
%right SUM PROD
%right TRANS
%nonassoc NEG
%nonassoc FST SND INL INR SUCC 
%nonassoc CASE ABORT
%left APP
%nonassoc ID LPAREN I0 I1 INTERVAL COE COM FILL HCOM HFILL ABS SIGMA NATREC LET PATHD PATH TRUE FALSE IF BOOL ZERO NAT STAR UNIT VOID REFL TYPE PLACEHOLDER WILDCARD LANGLE
%nonassoc SYMM

%start command
%type <Ast.command> command
%type <Ast.proof> decl
%type <((string list * Ast.expr) * bool) list> ctx
%type <Ast.level> level
%type <Ast.expr> expr
%type <Ast.expr> app_expr
%type <Ast.expr> head_expr
%type <Ast.expr> face_expr
%type <Ast.expr> face_head
%type <Ast.expr> atom
%type <string list> ids
%type <string list> vars
%type <((string * expr) list) * expr> blocks

%%

command:  
  | decl command                                            {Thm($2, $1)}
  | IND ID ctx expr COLONEQ constr command                  {Ind($7, $2, $3, $4, $6)}
  | IMPORT FILENAME command                                 {Import($3, $2)}
  | UNIVERSE ids command                                    {Level($3, $2)}
  | PRINT ID command                                        {Print($3, $2)}
  | EVAL expr command                                       {Eval($3, $2)}
  | EOF                                                     {Eof()}

decl:
  | DEF ID ctx expr COLONEQ expr                            {Prf($2, $3, $4, $6)}
  | INFER ctx expr                                          {Prf("", $2, Ast.Hole("0", []), $3)}

constr: 
  | BAR ID COLON expr                                       {[($2, $4)]}
  | BAR ID COLON expr constr                                {(($2, $4) :: $5)}

ctx: 
  | LPAREN ids COLON expr RPAREN ctx                         {(($2, $4), true) :: $6}
  | LBRACE ids COLON expr RBRACE ctx                         {(($2, $4), false) :: $6}
  | VDASH                                                   {([])}

ids:
  | ID                                                      { [$1] }
  | ID ids                                                  { $1 :: $2 }

vars:
  | ID                                                      { [$1] }
  | WILDCARD                                                { ["v?"] }
  | ID vars                                                 { $1 :: $2 }
  | WILDCARD vars                                           { "v?" :: $2 }

blocks:
  | expr %prec PI                                          { ([], $1) }
  | LPAREN ids COLON expr RPAREN blocks                    { (ids_to_bindings $2 $4 @ fst $6, snd $6) }

level:
  | ID                                                     { Var ($1) }
  | NUMBER                                                 { Num (int_of_string ($1)) }
  | NEXT level                                             { Suc ($2) }
  | MAX level level                                        { Max ($2, $3) }
  | LPAREN level RPAREN                                    { $2 }

expr: 
  | app_expr %prec NEG                                      { $1 }
  | expr RARROW expr                                        { Pi("v?",$1,$3) }
  | expr LRARROW expr                                       { Sigma("v?", Pi("v?",$1,$3), Pi("v?",$3,$1)) }
  | expr PROD expr                                          { Sigma("v?",$1,$3) }
  | expr SUM expr                                           { Sum($1,$3) }
  | expr AT expr                                            { At($1,$3) }
  | expr SYMM                                               { App(Id "path_symm", $1) }
  | expr TRANS expr                                         { App(App(Id "path_trans", $1), $3) }

app_expr:
  | head_expr                                               { $1 }
  | app_expr head_expr %prec APP                            { App($1,$2) }

head_expr:
  | atom                                                    { $1 }
  | APP head_expr head_expr                                 { App($2,$3) }
  | COE head_expr head_expr head_expr head_expr             { Coe($2,$3,$4,$5) }
  | COM head_expr head_expr head_expr head_expr
    BAR I0 RARROW face_expr
    BAR I1 RARROW face_expr                                 { App (fill_def ($2) ($3) ($4) ($5) ($9) ($13), I1()) }
  | FILL head_expr head_expr head_expr head_expr
    BAR I0 RARROW face_expr
    BAR I1 RARROW face_expr                                 { fill_def ($2) ($3) ($4) ($5) ($9) ($13) }
  | HCOM head_expr
    BAR I0 RARROW face_expr
    BAR I1 RARROW face_expr %prec CASE                      { App(Hfill($2,$6,$10),I1()) }
  | HFILL head_expr
    BAR I0 RARROW face_expr
    BAR I1 RARROW face_expr %prec CASE                      { Hfill($2,$6,$10) }
  | ABS vars COMMA expr %prec PI                            { abs_of_list ($4) ($2) }
  | ABS LPAREN ids COLON expr RPAREN COMMA expr %prec PI   { Abs(single_id $3,$8) }
  | PI blocks                                               { pi_of_list (snd $2) (fst $2) }
  | FST head_expr                                           { Fst($2) }
  | SND head_expr                                           { Snd($2) }
  | SIGMA blocks                                            { sigma_of_list (snd $2) (fst $2) }
  | INL head_expr                                           { Inl($2) }
  | INR head_expr                                           { Inr($2) }
  | CASE head_expr head_expr head_expr %prec CASE           { Case($2,$3,$4) }
  | IF head_expr head_expr head_expr %prec CASE             { If($2,$3,$4) }
  | SUCC head_expr                                          { Succ($2) }
  | NATREC head_expr head_expr head_expr %prec ABORT        { Natrec($2,$3,$4) }
  | LET head_expr head_expr %prec ABORT                     { Let($2,$3) }
  | ABORT head_expr %prec ABORT                             { Abort($2) }
  | NEG app_expr %prec NEG                                  { Pi("v?",$2,Void()) }
  | LANGLE ID RANGLE expr %prec PI                          { Pabs($2,$4) }
  | LANGLE WILDCARD RANGLE expr %prec PI                    { Pabs("v?",$4) }
  | PATHD head_expr head_expr head_expr %prec ABORT         { Pathd($2,$3,$4) }
  | PATH head_expr head_expr head_expr %prec ABORT          { Pathd(Abs("v?",$2),$3,$4) }

face_expr:
  | face_head                                               { $1 }
  | atom atom %prec APP                                     { App($1,$2) }
  | face_expr RARROW face_expr                              { Pi("v?",$1,$3) }
  | face_expr LRARROW face_expr                             { Sigma("v?", Pi("v?",$1,$3), Pi("v?",$3,$1)) }
  | face_expr PROD face_expr                                { Sigma("v?",$1,$3) }
  | face_expr SUM face_expr                                 { Sum($1,$3) }
  | face_expr AT face_head                                  { At($1,$3) }
  | face_expr SYMM                                          { App(Id "path_symm", $1) }
  | face_expr TRANS face_expr                               { App(App(Id "path_trans", $1), $3) }

face_head:
  | atom %prec NEG                                          { $1 }
  | APP face_head face_head                                 { App($2,$3) }
  | COE face_head face_head face_head face_head             { Coe($2,$3,$4,$5) }
  | COM face_head face_head face_head face_head
    BAR I0 RARROW face_expr
    BAR I1 RARROW face_expr                                 { App (fill_def ($2) ($3) ($4) ($5) ($9) ($13), I1()) }
  | FILL face_head face_head face_head face_head
    BAR I0 RARROW face_expr
    BAR I1 RARROW face_expr                                 { fill_def ($2) ($3) ($4) ($5) ($9) ($13) }
  | HCOM face_head
    BAR I0 RARROW face_expr
    BAR I1 RARROW face_expr %prec CASE                      { App(Hfill($2,$6,$10),I1()) }
  | HFILL face_head
    BAR I0 RARROW face_expr
    BAR I1 RARROW face_expr %prec CASE                      { Hfill($2,$6,$10) }
  | ABS vars COMMA face_expr %prec PI                       { abs_of_list ($4) ($2) }
  | ABS LPAREN ids COLON expr RPAREN COMMA face_expr %prec PI { Abs(single_id $3,$8) }
  | PI blocks                                               { pi_of_list (snd $2) (fst $2) }
  | FST face_head                                           { Fst($2) }
  | SND face_head                                           { Snd($2) }
  | SIGMA blocks                                            { sigma_of_list (snd $2) (fst $2) }
  | INL face_head                                           { Inl($2) }
  | INR face_head                                           { Inr($2) }
  | CASE face_head face_head face_head %prec CASE           { Case($2,$3,$4) }
  | IF face_head face_head face_head %prec CASE             { If($2,$3,$4) }
  | SUCC face_head                                          { Succ($2) }
  | NATREC face_head face_head face_head %prec ABORT        { Natrec($2,$3,$4) }
  | LET face_head face_head %prec ABORT                     { Let($2,$3) }
  | ABORT face_head %prec ABORT                             { Abort($2) }
  | NEG face_expr                                           { Pi("v?",$2,Void()) }
  | LANGLE ID RANGLE face_expr %prec PI                     { Pabs($2,$4) }
  | LANGLE WILDCARD RANGLE face_expr %prec PI               { Pabs("v?",$4) }
  | PATHD face_head face_head face_head %prec ABORT         { Pathd($2,$3,$4) }
  | PATH face_head face_head face_head %prec ABORT          { Pathd(Abs("v?",$2),$3,$4) }

atom:
  | ID                                                      { Id($1) }
  | LPAREN expr RPAREN                                      { $2 }
  | I0                                                      { I0() }
  | I1                                                      { I1() }
  | INTERVAL                                                { Int() }
  | LPAREN expr COMMA expr RPAREN                           { Pair($2,$4) }
  | TRUE                                                    { True() }
  | FALSE                                                   { False() }
  | BOOL                                                    { Bool() }
  | ZERO                                                    { Zero() }
  | NAT                                                     { Nat() }
  | STAR                                                    { Star() }
  | UNIT                                                    { Unit() }
  | VOID                                                    { Void() }
  | REFL                                                    { Pabs("v?", Wild 0) }
  | TYPE ZERO                                               { Type(Num 0) }
  | TYPE level                                              { Type ($2) }
  | PLACEHOLDER NUMBER                                      { Hole($2, []) }
  | WILDCARD                                                { Wild 0 }
  | SUBGOAL                                                 { Subgoal() }
