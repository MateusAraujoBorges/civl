all: sort sortBad

sort: pairInsertSort_partial.cvl
	contract verify -collectSymbolicConstants $<

sortBad: pairInsertSort_partial-bad_assert.cvl
	contract verify -collectSymbolicConstants $<

clean:
	rm -rf *~ CIVLREP SARL_Why3