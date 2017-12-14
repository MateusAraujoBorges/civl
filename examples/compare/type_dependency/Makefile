CIVL = civl
COMPARE = $(CIVL) compare

all: test

test: impl.c spec.c
	$(COMPARE) -impl impl.c -spec spec.c 

clean: 
	rm -f *~
	rm -f -r CIVLREP
