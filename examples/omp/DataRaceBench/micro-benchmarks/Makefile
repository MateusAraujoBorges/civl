CIVL=civl
OPTIONS=-input_omp_thread_max=2
VERIFY=$(CIVL) verify $(OPTIONS)

.IGNORE=polybench.c

all: $(patsubst %.c, check_%, $(wildcard *.c))

check_%: %.c
	echo Check data race for $<
	$(VERIFY) $<  2>&1  ## redirect err to wherever stdout going

clean: 
	rm -rf *~ CIVLREP *OUT.txt ProverOutput.txt
