CIVL=civl
VERIFY=$(CIVL) verify -collectSymbolicConstants

all: loop

loop:  max.cvl
	$(VERIFY) $<

bad1:  max-bad_assert.cvl
	$(VERIFY) $<

bad2:  max-bad_invariant.cvl
	$(VERIFY) $<

clean:
	rm -rf CIVLREP SARL_Why3 *~