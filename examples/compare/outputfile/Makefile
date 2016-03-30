CIVL = civl
COMPARE = $(CIVL) compare

all: file

file: spec.c impl.c
	$(COMPARE) -spec spec.c -impl impl.c

clean: 
	rm -f *~
	rm -f -r CIVLREP
