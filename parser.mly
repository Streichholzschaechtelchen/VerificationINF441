%token INT SEMICOLON COMMA BEG END COLON OPBR GEQ LEQ GT LT EQ ZERO CLBR EQUALS IF ELSE WHILE AND TIMES PLUS MINUS
%token <int> NUMBER
%token <string> VAR
%start progc
%type <Types.prog> progc
   
%%   

progc: INT list_var SEMICOLON block { $2, $4 };

list_var:
         VAR                { [$1] }
	|VAR COMMA list_var { $1::$3 }
	;

block: /*type block = (inv list) * (instr list)*/
       /*empty*/                     { [], [] }
      |BEG inv END instr BEG inv END { $2::[$6], [$4] }
      |BEG inv END instr block       { $2::(fst $5), $4::(snd $5) }
      ;

ineq: /*type ineq = (int * int) list*/
     expr GEQ ZERO { [$1] }
    |expr LEQ ZERO { [List.map (fun x -> fst x, -snd x) $1] }
    |expr GT ZERO  { [(None, -1)::$1] }
    |expr LT ZERO  { [(None, 1)::$1] }
    |expr EQ ZERO  { [$1; List.map (fun x -> fst x, -snd x) $1] }

instr:
      VAR EQUALS expr SEMICOLON                         { Types.Assignment ($1, $3) }
     |IF OPBR inv CLBR BEG block END ELSE BEG block END { Types.If ($3, $6, $10) }
     |WHILE OPBR inv CLBR BEG block END                 { Types.While ($3, $6) }
     ;

inv: /*type inv = ineq list*/
    /*empty*/    { [] }   
   |ineq         { $1 }
   |ineq AND inv { $1@$3 }
   ;

atom_expr: /*type atom_expr = var option * int*/
          VAR                      { Some ($1), 1 }
         |MINUS VAR                { Some ($2), -1 }
	 |NUMBER                   { None, $1 }
	 |NUMBER TIMES VAR         { Some ($3), $1 }
	 |VAR TIMES NUMBER         { Some ($1), $3 }
	 |NUMBER TIMES NUMBER      { None, $1 * $3 }
	 ;
	   
expr: /*type expr = atom_expr list*/
     atom_expr           { [$1] }
    |expr PLUS atom_expr { $3::$1 }
    |expr MINUS atom_expr{ ( fst $3, - snd $3 )::$1 } /*conflicts?*/
    ;

%%
