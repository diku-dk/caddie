
MLKIT ?= mlkit

all: ad.exe
	./ad.exe

ad.exe: ad.mlb *.sig *.sml
	$(MLKIT) -o $@ $<

clean:
	rm -rf *~ MLB *.exe run
