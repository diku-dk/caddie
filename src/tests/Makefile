RESFILES_ALL=ad_ex0.res ad_ex1.res ba.res rad_ex0.res rad_ex1.res

MLCOMP ?= mlkit

.PHONY: all
all: test

.PHONY: clean
clean:
	rm -rf *~ MLB run log.txt *.exe *.out *.res

.PHONY: test
test: $(RESFILES_ALL)
	@echo "-------T E S T --- R E P O R T-------"
	@cat $(RESFILES_ALL)
	@echo "-------T E S T --- S U M M A R Y-----"
	@echo "Tests succeeded:   `grep "OK" $(RESFILES_ALL) | wc -l` /`grep "Test" $(RESFILES_ALL) | wc -l`"
	@echo "Test errors:       `grep "ERR" $(RESFILES_ALL) | wc -l` /`grep "Test" $(RESFILES_ALL) | wc -l`"
	@echo "See log.txt"
	@echo "-------------------------------------"
	@exit `grep "ERR" $(RESFILES_ALL) | wc -l`

%.out: %.exe
	./$< > $@

%.exe: %.mlb *.sml
	$(MLCOMP) -output $@ $<

%.res: %.out
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
	@cat $@ >> log.txt
