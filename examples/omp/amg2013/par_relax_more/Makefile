.PHONY:amg2013

CIVL=civl

INCLUDES=.:../AMG2013:../AMG2013/IJ_mv:../AMG2013/krylov:../AMG2013/parcsr_ls:../AMG2013/parcsr_mv:../AMG2013/seq_mv:../AMG2013/sstruct_mv:../AMG2013/struct_mv:../AMG2013/test:../AMG2013/utilities:

SHOWV=${CIVL} show -verbose 
SHOW=${CIVL} show 
VERIFY=${CIVL} verify 

all: 
	${SHOW} -userIncludePath=${INCLUDES} -DHYPRE_SEQUENTIAL -DHYPRE_USING_OPENMP main.c ../AMG2013/parcsr_ls/par_relax_more.c hypre_memory.c

clean: 
