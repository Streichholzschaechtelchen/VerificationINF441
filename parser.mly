%token INT SEMICOLON COMMA BEG END COLON OPBR GEQ LEQ GT LT EQ ZERO CLBR EQUALS IF ELSE WHILE AND OR NOT TIMES PLUS MINUS EOF
%token <int> NUMBER
%token <string> VAR
%left OR
%left AND
%start progc
%type <Types.pprog> progc
		      
   
%%   

progc: INT list_var SEMICOLON block EOF { $2, $4 }
     ;

list_var:
         VAR                { [$1] }
	|VAR COMMA list_var { $1::$3 }
	;

block:
       /*empty*/                     { [], [] }
      |instr                         { [Types.Naught ((Parsing.rhs_start_pos 1).Lexing.pos_lnum);
					Types.Naught ((Parsing.rhs_start_pos 1).Lexing.pos_lnum)],
				       [$1] }
      |instr BEG inv END             { [Types.Naught ((Parsing.rhs_start_pos 1).Lexing.pos_lnum);
					$3], [$1] }
      |BEG inv END instr BEG inv END { [$2; $6], [$4] }
      |instr block                   { (Types.Naught ((Parsing.rhs_start_pos 1).Lexing.pos_lnum))::(fst $2),
				       $1::(snd $2) }
      |BEG inv END instr block       { $2::(fst $5), $4::(snd $5) }
      ;

ineq:
     expr GEQ expr { [ParserAux.assemble_inequality $1 $3] }
    |expr LEQ expr { [ParserAux.assemble_inequality $3 $1] }
    |expr GT expr  { [ParserAux.assemble_inequality ~strict:true $1 $3] }
    |expr LT expr  { [ParserAux.assemble_inequality ~strict:true $3 $1] }
    |expr EQ expr  { [ParserAux.assemble_inequality $1 $3; ParserAux.assemble_inequality $3 $1] }

instr:
      VAR EQUALS expr SEMICOLON                         { Types.PAssignment ($1, $3) }
     |IF OPBR inv CLBR BEG block END ELSE BEG block END { Types.PIf ($3, $6, $10) }
     |WHILE OPBR inv CLBR BEG block END                 { Types.PWhile ($3, $6) }
     ;

inv:
    /*empty*/     { Types.Naught ((Parsing.rhs_start_pos 1).Lexing.pos_lnum) }
   |ineq          { let lnum = (Parsing.rhs_start_pos 1).Lexing.pos_lnum in
		      match $1 with
			[i]     -> Types.Expr (lnum, i)
		      | i::j::t -> ParserAux.assemble_and lnum (Types.Expr (lnum, i)) (Types.Expr (lnum, j))
		      | _       -> failwith "This should never occur"
	          }
   |OPBR inv CLBR { $2 }
   |NOT inv       { Types.Not ((Parsing.rhs_start_pos 1).Lexing.pos_lnum, $2) }
   |inv AND inv   { ParserAux.assemble_and (Parsing.rhs_start_pos 1).Lexing.pos_lnum $1 $3 }
   |inv OR inv    { ParserAux.assemble_or (Parsing.rhs_start_pos 1).Lexing.pos_lnum $1 $3 }
   ;

atom_expr:
          VAR                      { Some ($1), 1 }
         |MINUS VAR                { Some ($2), -1 }
	 |NUMBER                   { None, $1 }
	 |NUMBER TIMES VAR         { Some ($3), $1 }
	 |VAR TIMES NUMBER         { Some ($1), $3 }
	 |NUMBER TIMES NUMBER      { None, $1 * $3 }
	 ;
	   
expr:
     atom_expr           { [$1] }
    |expr PLUS atom_expr { $3::$1 }
    |expr MINUS atom_expr{ ( fst $3, - snd $3 )::$1 }
    ;

%%
