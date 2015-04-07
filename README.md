DogIR
-----

Prerequisites: opam, menhir, ocamlgraph

Build:
$ ocamlbuild -libs graph -lflags -I,$HOME/.opam/system/lib/ocamlgraph -use-ocamlfind -use-menhir top.native

Simple test:

$ ./top.native -i tests/mp_load-load.dog -emitir
