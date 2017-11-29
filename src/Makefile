
all: main.cmi
	ocamlfind ocamlopt -o pumpkin-git -linkpkg -thread -package core,str main.ml

main.cmi:
	ocamlfind ocamlopt -o pumpkin-git -linkpkg -thread -package core,str main.mli

clean:
	rm main.{cmx,cmi,o} pumpkin-git
