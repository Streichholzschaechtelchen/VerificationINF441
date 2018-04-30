{
  open Parser
  exception Eof
}

  rule token = parse
     [' ' '\t' '\n']+                                         {token lexbuf}
    |"int"	                                              {INT}
    |';'                                                      {SEMICOLON}
    |','                                                      {COMMA}
    |'{'                                                      {BEG}
    |'}'                                                      {END}
    |'('                                                      {OPBR}
    |')'                                                      {CLBR}
    |">="                                                     {GEQ}
    |"<="                                                     {LEQ}
    |">"                                                      {GT}
    |"<"                                                      {LT}
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
    |eof                                                      {raise Eof}

{}
