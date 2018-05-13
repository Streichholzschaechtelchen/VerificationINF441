%token INT SEMICOLON COMMA BEG END COLON OPBR GEQ LEQ GT LT EQ ZERO CLBR EQUALS IF ELSE WHILE AND TIMES PLUS MINUS EOF
%token <int> NUMBER
%token <string> VAR
%start progc
%type <Types.pprog> progc
   
%%   

progc: INT list_var SEMICOLON block EOF { $2, $4 }
     ;

list_var:
         VAR                { [$1] }
	|VAR COMMA list_var { $1::$3 }
	;

block: /*type pblock = (inv list) * (pinstr list)*/
       /*empty*/                     { [], [] }
      |BEG inv END instr BEG inv END { $2::[$6], [$4] }
      |BEG inv END instr block       { $2::(fst $5), $4::(snd $5) }
      ;

ineq: /*type pineq = (Some var * int) list*/
     expr GEQ ZERO { [$1] }
    |expr LEQ ZERO { [((fst $1), List.map (fun x -> fst x, -snd x) (snd $1))] }
    |expr GT ZERO  { [((fst $1), (None, -1)::(snd $1))] }
    |expr LT ZERO  { [((fst $1), (None, -1)::(List.map (fun x -> fst x, -snd x) (snd $1)))] }
    |expr EQ ZERO  { [$1;((fst $1),List.map(fun x -> fst x, -snd x)(snd $1))] }

instr:
      VAR EQUALS expr SEMICOLON                         { Types.PAssignment ($1, $3) }
     |IF OPBR inv CLBR BEG block END ELSE BEG block END { Types.PIf ($3, $6, $10) }
     |WHILE OPBR inv CLBR BEG block END                 { Types.PWhile ($3, $6) }
     ;

inv: /*type pinv = pineq list*/
    /*empty*/    { [] }   
   |ineq         { $1 }
   |ineq AND inv { $1@$3 }
   ;

atom_expr: /*type patom_expr = pvar option * int*/
          VAR                      { Some ($1), 1 }
         |MINUS VAR                { Some ($2), -1 }
	 |NUMBER                   { None, $1 }
	 |NUMBER TIMES VAR         { Some ($3), $1 }
	 |VAR TIMES NUMBER         { Some ($1), $3 }
	 |NUMBER TIMES NUMBER      { None, $1 * $3 }
	 ;
	   
expr: /*type pexpr = int * patom_expr list*/
     atom_expr           { (Parsing.rhs_start_pos 1).Lexing.pos_lnum, [$1] }
    |expr PLUS atom_expr { (fst $1), $3::(snd $1) }
    |expr MINUS atom_expr{ (fst $1), ( fst $3, - snd $3 )::(snd $1) }
    ;

%%
