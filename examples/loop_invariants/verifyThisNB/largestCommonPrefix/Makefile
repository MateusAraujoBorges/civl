CIVL=civl
VERIFY=$(CIVL) verify -collectSymbolicConstants

all: loop

loop:  lcp.c
	$(VERIFY) $<

verify_%: %.c
	$(VERIFY) $<

clean:
	rm -rf CIVLREP *~ SARL_Why3