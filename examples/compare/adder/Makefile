CIVL = civl
COMPARE = $(CIVL) compare

all: adder

adder: adder_par.c adder_spec.c
	$(COMPARE) -inputNB=10 -input_mpi_nprocs_hi=4 -impl adder_par.c -spec adder_spec.c

clean: 
	rm -f *~
	rm -f -r CIVLREP