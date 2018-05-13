{
  open Parser

  (*inspired by A. Bonenfant, Aide-mémoire Ocamllex & Ocamlyacc, 2010*)
  let incr_line lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- { pos with
				  Lexing.pos_lnum = pos.Lexing.pos_lnum + 1 }
						 
}

  rule token = parse
     [' ' '\t']                                               {token lexbuf}
    |'\n'                                                     {incr_line lexbuf;
							       token lexbuf}
    |"int"	                                              {INT}
    |';'                                                      {SEMICOLON}
    |','                                                      {COMMA}
    |'{'                                                      {BEG}
    |'}'                                                      {END}
    |'('                                                      {OPBR}
    |')'                                                      {CLBR}
    |">="                                                     {GEQ}
    |"<="                                                     {LEQ}
    |'>'                                                      {GT}
    |'<'                                                      {LT}
    |"=="                                                     {EQ}
    |'0'                                                      {ZERO}
    |'='                                                      {EQUALS}
    |"if"                                                     {IF}
    |"else"                                                   {ELSE}
    |"while"                                                  {WHILE}
    |"and"                                                    {AND}
    |'*'                                                      {TIMES}
    |'+'                                                      {PLUS}
    |'-'                                                      {MINUS}
    |['-']?['1'-'9']['0'-'9']* as n                           {NUMBER (int_of_string n)}
    |['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '_' '0'-'9']* as s {VAR(s)}
    |eof                                                      {EOF}

{}
