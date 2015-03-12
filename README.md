DogIR
-----

Build:
$ ocamlbuild -use-menhir top.native

Simple test:

$ cat mp_load-load.dog  | ./top.native
