all: linlang

clean:
	rm *.cm* lexer.ml parser.ml parser.mli

linlang: parser lexer simplex linlang.ml
	ocamlopt -o linlang types.ml parser.ml lexer.ml parser.mli simplex.ml linlang.ml

types: types.ml simplex
	ocamlopt -c types.ml

lexer.ml: lexer.mll
	ocamllex lexer.mll

lexer: parser lexer.ml
	ocamlopt -c lexer.ml

parser.mli: parser.mly
	ocamlyacc parser.mly

parser.ml: parser.mli
	ocamlopt -c parser.mli

parser: types parser.ml
	ocamlopt -c parser.ml

simplex: simplex.ml
	ocamlopt -c simplex.ml
