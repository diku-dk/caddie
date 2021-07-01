
.PHONY: prepare
prepare:
	smlpkg sync

.PHONY: all
all: cad

.PHONY: cad
cad:
	mlkit -output $@ cad.mlb

.PHONY: test
test:
	$(MAKE) -C tests all

.PHONY: clean
clean:
	rm -rf *~ MLB *.exe run cad
	$(MAKE) -C tests clean
