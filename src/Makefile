
all: main.cmi
	ocamlfind ocamlopt -o gitter -linkpkg -thread -package core,str main.ml

main.cmi:
	ocamlfind ocamlopt -o gitter -linkpkg -thread -package core,str main.mli

clean:
	rm main.{cmx,cmi,o} gitter
