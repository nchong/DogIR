top.native: *.ml
	ocamlbuild -libs graph -lflags -I,`ocamlfind query ocamlgraph` -use-ocamlfind -use-menhir top.native

.PHONY: clean
clean:
	ocamlbuild -clean
