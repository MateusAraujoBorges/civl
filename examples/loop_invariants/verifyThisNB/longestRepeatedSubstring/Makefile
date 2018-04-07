CIVL=civl
OPTION=-collectSymbolicConstants=true
VERIFY=$(CIVL) verify $(OPTION) 

all : loop

loop: lrs_deductive.cvl
	$(VERIFY) $<

verify_%:  %.cvl
	$(VERIFY) $<

clean:
	rm -rf CIVLREP SARL_Why3 *~