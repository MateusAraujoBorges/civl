CIVL=civl
VERIFY=$(CIVL) verify -collectSymbolicConstants

all: loop

loop:  two_equal_elements.cvl
	$(VERIFY) $<

bad1:  two_equal_elements-bad_assert.cvl  two_equal_elements-bad_invariant.cvl
	$(VERIFY) $<

bad2:  two_equal_elements-bad_invariant.cvl
	$(VERIFY) $<

clean:
	rm -rf CIVLREP SARL_Why3 *~