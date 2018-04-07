CIVL=civl
OPTION=-collectSymbolicConstants=true
VERIFY=$(CIVL) verify $(OPTION) 

all : loop

loop : pairInsertSort_partial.cvl
	$(VERIFY) $<

verify_%:  %.cvl
	$(VERIFY) $<

clean:
	rm -rf CIVLREP SARL_Why3 *~