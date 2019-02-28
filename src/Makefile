
.PHONY: all
all: mosml

.PHONY: mosml
mosml:
	mosml -P full diff.sml

.PHONY: mlkit
mlkit:
	mlkit -o diff.exe diff.sml
	./diff.exe

.PHONY: clean
clean:
	rm -rf MLB *~ run
