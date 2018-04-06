CIVL=civl
OPTION=-collectSymbolicConstants=true
VERIFY=$(CIVL) verify $(OPTION) 

all : $(patsubst %.cvl, verify_%, $(wildcard *))

verify_%:  %.cvl
	$(VERIFY) $<

clean:
	rm -rf CIVLREP *~
