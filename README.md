DogIR
-----

Prerequisites: opam, menhir, ocamlgraph

Build:

$ make

Simple test:

$ ./top.native -i tests/mp_load-load.dog -emitir

Notes
-----

* Dogs encode a path priority (attached to the end state of an edge). We assume
  a two-priority scheme.
