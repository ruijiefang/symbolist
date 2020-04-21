LIBS := unix,str

all: main.native

main.native:
	ocamlbuild -libs $(LIBS) main.native 

clean: 
	ocamlbuild -clean

