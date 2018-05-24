CIVL=civl
ABC=abc
PARSE=$(ABC)
NP=-input_mpi_nprocs=2
VERIFY=$(CIVL) verify $(NP)


all: parse

parse: allreduce.c allreduce.h
	$(PARSE) allreduce.c

verify: allreduce.c allreduce.h
	$(VERIFY) allreduce.c

run:  allreduce.c allreduce.h
	$(VERIFY) driver.cvl allreduce.c

clean:
	rm -rf CIVLREP *~