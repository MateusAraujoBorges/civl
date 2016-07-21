CIVL = civl
COMPARE = $(CIVL) compare

all: output

output: ex2Driver.c ex2a.c ex2b.c
	$(COMPARE) -impl ex2Driver.c ex2a.c -spec ex2Driver.c ex2b.c 

clean: 
	rm -f *~
	rm -f -r CIVLREP
