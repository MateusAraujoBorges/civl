CIVL=civl
OPTION=-errorBound=10 -enablePrintf=false -mpiContract
VERIFY=$(CIVL) verify $(OPTION)


all: $(patsubst  %.c, VERIFY_%, $(wildcard *.c))

VERIFY_%: %.c
	$(VERIFY) $<

clean:
	rm -r -f *~ CIVLREP