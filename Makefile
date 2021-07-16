
.PHONY: all
all:
	$(MAKE) -C src all

.PHONY: clean
clean:
	rm -f *~
	$(MAKE) -C src clean

.PHONY: test
test:
	$(MAKE) -C src test
