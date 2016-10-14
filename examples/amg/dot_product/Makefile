CIVL=civl
VERIFY=$(CIVL) verify $(NP)
NP=-input_mpi_nprocs=5
DEBUG=-DDEBUG

all: civl_run_debug


civl_run: dot_product.c
	$(VERIFY) dot_product.c

civl_run_debug: dot_product.c
	$(VERIFY) $(DEBUG) dot_product.c

clean:
	rm -rf *~ CIVLREP