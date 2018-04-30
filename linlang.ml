
let _ =
  try
    let lexbuf = Lexing.from_channel stdin in
    let _ = Parser.progc Lexer.token lexbuf in
    ()
  with Lexer.Eof ->
    print_string "coucou\n"
