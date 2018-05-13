all: linlang

clean:
	rm *.cm* *.o lexer.ml parser.ml parser.mli

linlang: parser lexer simplex types printer fourrierMotzkin linlang.ml
	ocamlopt -o linlang types.ml parser.ml lexer.ml parser.mli simplex.ml printer.ml fourrierMotzkin.ml linlang.ml

types: types.ml simplex
	ocamlopt -c types.ml

printer: printer.ml printer.cmi
	ocamlopt -c printer.ml

printer.cmi: printer.mli types
	ocamlopt -c printer.mli

fourrierMotzkin: fourrierMotzkin.ml fourrierMotzkin.cmi simplex
	ocamlopt -c fourrierMotzkin.ml

fourrierMotzkin.cmi: fourrierMotzkin.mli types
	ocamlopt -c fourrierMotzkin.mli

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
