TESTS=test0 test1 test2 test3 simple ba zero num add smul

TESTFILES=$(TESTS:%=%.cad)
RESFILES=$(TESTFILES:%.cad=%.res)

CAD?=../cad

.PHONY: all
all: test

.PHONY: tst
tst:
	echo $(RESFILES)

%.out: %.cad ../cad
	$(CAD) --Ptyped --Pexp $< > $@ 2>&1; echo "done" >> /dev/null

%.res: %.out %.out.ok
	@(diff -aq $< $*.out.ok > /dev/null 2>&1; \
         if [ $$? -eq 0 ]; then \
             echo "Test $*: OK" > $@ \
         ; else \
             if [ -e $*.out.ok ]; then \
                echo "Test $*: *** ERR: file $< differs from $*.out.ok ***" > $@ \
             ; else \
                echo "Test $*: *** ERR: file $*.out.ok does not exist ***" > $@ \
             ; fi \
         ; fi)
	@cat $@
	@cat $@ >> complog.txt

.PHONY: test
test: $(RESFILES)
	@echo "-------T E S T --- R E P O R T-------"
	@../cad --version
	@cat $(RESFILES)
	@echo "Tests succeeded:   `grep "OK" $(RESFILES) | wc -l` /`grep "Test" $(RESFILES) | wc -l`"
	@echo "Test errors:       `grep "ERR" $(RESFILES) | wc -l` /`grep "Test" $(RESFILES) | wc -l`"
	@echo "See complog.txt"
	@echo "-------------------------------------"
	@exit `grep "ERR" $(RESFILES) | wc -l`

../cad:
	$(MAKE) -C .. cad

.PHONY: clean
clean:
	rm -rf *~ *.exe *.res *.out complog.txt
