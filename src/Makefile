
MLCOMP?=mlkit
SMLPKG?=smlpkg

.PHONY: all
all: cad

.PHONY: cad
cad: lib
	$(MLCOMP) -output $@ cad.mlb

.PHONY: test
test: lib
	$(MAKE) -C tests all
	$(MAKE) -C examples test

.PHONY: clean
clean:
	rm -rf *~ MLB *.exe run cad
	$(MAKE) -C tests clean

.PHONY: realclean
realclean: clean
	rm -rf lib

lib: sml.pkg
	$(SMLPKG) sync
