%{
(**
  (c) Copyright 2019 Bruno Bentzen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Desc: The parser of the program. The file is parsed into the objects 
        of the raw expression type (expressions with named variables) 
        and commands on them (see Ast). Raw expressions are later converted 
        into the core expression type with locally nameless representation.
 **)

open Ast

let rec abs_of_list e = function
  | [] -> e
  | id :: l ->
    Ast.RLam(id, abs_of_list e l)

let rec pi_of_list e = function
  | [] -> e
  | (id, ty) :: l ->
    Ast.RPi (id, ty, pi_of_list e l)

let rec sigma_of_list e = function
  | [] -> e
  | (id, ty) :: l ->
    Ast.RSigma (id, ty, sigma_of_list e l)

let rec ids_to_bindings ids ty =
  match ids with
  | [] -> []
  | id :: rest -> (id, ty) :: ids_to_bindings rest ty

let fill_def i j ty e e1 e2 =
  let v1 = fresh_var (RApp(e1, e2)) e 2 in
  RHcom(i, j, RLam(v1, RCoe (i, j, ty, RApp(e, RId v1))), 
  RLam(v1, RCoe (RId v1, j, ty, RApp(e1, RId v1))),
  RLam(v1, RCoe (RId v1, j, ty, RApp(e2, RId v1))))

let single_id = function
  | [id] -> id
  | _ -> failwith "Expected exactly one identifier before ':'"

%}

%token <string> ID
%token <string> FILENAME
%token <string> NUMBER
%token EVAL IMPORT IND UNIVERSE DEF PRINT INFER LBRACE RBRACE
%token TYPE MAX NEXT COLON
%token I0 I1 INTERVAL COE HCOM COM BAR
%token ABS APP RARROW LRARROW PI
%token LPAREN RPAREN COMMA FST SND PROD SIGMA
%token ZERO NAT
%token STAR SUM
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
%nonassoc FST SND 
%nonassoc ABORT
%left APP
%nonassoc ID LPAREN I0 I1 INTERVAL COE COM HCOM ABS SIGMA PATHD PATH ZERO NAT STAR VOID REFL TYPE PLACEHOLDER WILDCARD LANGLE
%nonassoc SYMM

%start command
%type <Ast.command> command
%type <Ast.proof> decl
%type <((string list * Ast.rawexpr) * bool) list> ctx
%type <Ast.rawlevel> level
%type <Ast.rawexpr> expr
%type <Ast.rawexpr> app_expr
%type <Ast.rawexpr> head_expr
%type <Ast.rawexpr> face_expr
%type <Ast.rawexpr> face_head
%type <Ast.rawexpr> atom
%type <string list> ids
%type <string list> vars
%type <((string * Ast.rawexpr) list) * Ast.rawexpr> blocks

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
  | INFER ctx expr                                          {Prf("infer", $2, RHole("0", []), $3)}

constr: 
  | BAR ID COLON expr                                       {[($2, $4)]}
  | BAR ID COLON expr constr                                {(($2, $4) :: $5)}

ctx: 
  | LPAREN ids COLON expr RPAREN ctx                         {(($2, $4), true) :: $6}
  | LBRACE ids COLON expr RBRACE ctx                         {(($2, $4), false) :: $6}
  | COLON                                                   {([])}

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
  | ID                                                     { RVar ($1) }
  | ZERO                                                   { RNum 0 }
  | NUMBER                                                 { RNum (int_of_string ($1)) }
  | NEXT level                                             { RSuc ($2) }
  | MAX level level                                        { RMax ($2, $3) }
  | LPAREN level RPAREN                                    { $2 }

expr: 
  | app_expr %prec NEG                                      { $1 }
  | expr RARROW expr                                        { RPi("v?",$1, $3) }
  | expr LRARROW expr                                       { RSigma("v?", RPi("v?",$1, $3), RPi("v?",$3, $1)) }
  | expr PROD expr                                          { RSigma("v?",$1, $3) }
  | expr SUM expr                                           { RApp(RApp(RId "sum", $1), $3) }
  | expr AT expr                                            { RAt($1,$3) }
  | expr SYMM                                               { RApp(RId "path_symm", $1) }
  | expr TRANS expr                                         { RApp(RApp(RId "path_trans", $1), $3) }

app_expr:
  | head_expr                                               { $1 }
  | app_expr head_expr %prec APP                            { RApp($1,$2) }

head_expr:
  | atom                                                    { $1 }
  | APP head_expr head_expr                                 { RApp($2,$3) }
  | COE atom atom head_expr head_expr                       { RCoe($2,$3,$4,$5) }
  | COM atom atom head_expr head_expr
    BAR I0 RARROW face_expr
    BAR I1 RARROW face_expr                                 { fill_def ($2) ($3) ($4) ($5) ($9) ($13) }
  | HCOM atom atom head_expr
    BAR I0 RARROW face_expr
    BAR I1 RARROW face_expr                                 { RHcom($2, $3, $4, $8, $12) }
  | ABS vars COMMA expr %prec PI                            { abs_of_list ($4) ($2) }
  | ABS LPAREN ids COLON expr RPAREN COMMA expr %prec PI    { RLam(single_id $3,$8) }
  | PI blocks                                               { pi_of_list (snd $2) (fst $2) }
  | FST head_expr                                           { RFst($2) }
  | SND head_expr                                           { RSnd($2) }
  | SIGMA blocks                                            { sigma_of_list (snd $2) (fst $2) }
  | ABORT head_expr %prec ABORT                             { RAbort($2) }
  | NEG app_expr %prec NEG                                  { RPi("v?", $2, RVoid()) }
  | LANGLE ID RANGLE expr %prec PI                          { RPabs($2, $4) }
  | LANGLE WILDCARD RANGLE expr %prec PI                    { RPabs("v?", $4) }
  | PATHD head_expr head_expr head_expr %prec ABORT         { RPathd($2, $3, $4) }
  | PATH head_expr head_expr head_expr %prec ABORT          { RPathd(RLam("v?", $2), $3, $4) }

face_expr:
  | face_head                                               { $1 }
  | atom atom %prec APP                                     { RApp($1, $2) }
  | face_expr RARROW face_expr                              { RPi("v?",$1, $3) }
  | face_expr LRARROW face_expr                             { RSigma("v?", RPi("v?",$1,$3), RPi("v?",$3,$1)) }
  | face_expr PROD face_expr                                { RSigma("v?",$1, $3) }
  | face_expr SUM face_expr                                 { RApp(RApp(RId "sum", $1), $3) }
  | face_expr AT face_head                                  { RAt($1,$3) }
  | face_expr SYMM                                          { RApp(RId "path_symm", $1) }
  | face_expr TRANS face_expr                               { RApp(RApp(RId "path_trans", $1), $3) }

face_head:
  | atom %prec NEG                                          { $1 }
  | APP face_head face_head                                 { RApp($2, $3) }
  | COE atom atom face_head face_head                       { RCoe($2, $3, $4, $5) }
  | COM atom atom face_head face_head
    BAR I0 RARROW face_expr
    BAR I1 RARROW face_expr                                 { fill_def ($2) ($3) ($4) ($5) ($9) ($13) }
  | HCOM atom atom face_head
    BAR I0 RARROW face_expr
    BAR I1 RARROW face_expr                                 { RHcom($2, $3, $4, $8, $12) }
  | ABS vars COMMA face_expr %prec PI                       { abs_of_list ($4) ($2) }
  | ABS LPAREN ids COLON expr RPAREN COMMA face_expr %prec PI { RLam(single_id $3,$8) }
  | PI blocks                                               { pi_of_list (snd $2) (fst $2) }
  | FST face_head                                           { RFst($2) }
  | SND face_head                                           { RSnd($2) }
  | SIGMA blocks                                            { sigma_of_list (snd $2) (fst $2) }
  | ABORT face_head %prec ABORT                             { RAbort($2) }
  | NEG face_expr                                           { RPi("v?", $2, RVoid()) }
  | LANGLE ID RANGLE face_expr %prec PI                     { RPabs($2, $4) }
  | LANGLE WILDCARD RANGLE face_expr %prec PI               { RPabs("v?", $4) }
  | PATHD face_head face_head face_head %prec ABORT         { RPathd($2, $3, $4) }
  | PATH face_head face_head face_head %prec ABORT          { RPathd(RLam("v?", $2), $3, $4) }

atom:
  | ID                                                      { RId($1) }
  | LPAREN expr RPAREN                                      { $2 }
  | I0                                                      { RI0() }
  | I1                                                      { RI1() }
  | INTERVAL                                                { RInt() }
  | LPAREN expr COMMA expr RPAREN                           { RPair($2, $4) }
  | ZERO                                                    { RId("zero") }
  | NAT                                                     { RId("nat") }
  | STAR                                                    { RId("star") }
  | VOID                                                    { RVoid() }
  | REFL                                                    { RPabs("v?", RWild 0) }
  | TYPE level                                              { RType ($2) }
  | PLACEHOLDER NUMBER                                      { RHole($2, []) }
  | WILDCARD                                                { RWild 0 }
  | SUBGOAL                                                 { RSubgoal() }