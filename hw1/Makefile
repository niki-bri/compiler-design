.PHONY: all test clean zip

SUBMIT := hellocaml.ml providedtests.ml
HWNAME := hw01
ZIPNAME := $(HWNAME)-submit.zip

main.native: $(SUBMIT)
	ocamlbuild -Is util -libs unix,str main.native

main.byte:
	ocamlbuild -Is util -libs unix,str main.byte

all: main.native

test: main.native
	./main.native --test

clean:
	ocamlbuild -clean

zip: $(SUBMIT)
	zip '$(ZIPNAME)' $(SUBMIT)
