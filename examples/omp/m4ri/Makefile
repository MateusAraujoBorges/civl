CIVL=civl
INCLUDES=-userIncludePath=./m4ri/ -sysIncludePath=./
SHOW=${CIVL} show -ompNoSimplify -ompLoopDecomp=ROUND_ROBIN -inputTHREAD_MAX=3 -enablePrintf=false 
VERIFY=${CIVL} verify -ompNoSimplify -ompLoopDecomp=ROUND_ROBIN -inputTHREAD_MAX=3 -enablePrintf=false 
VERIFYALL=${CIVL} verify -ompNoSimplify -ompLoopDecomp=ALL -inputTHREAD_MAX=3 -enablePrintf=false 
SIMPLIFY=${CIVL} verify -ompLoopDecomp=ALL -inputTHREAD_MAX=3 -enablePrintf=false 

M4RI=m4ri/brilliantrussian.c m4ri/debug_dump.c m4ri/djb.c m4ri/echelonform.c m4ri/graycode.c m4ri/io.c m4ri/misc.c m4ri/mmc.c m4ri/mp.c m4ri/mzd.c m4ri/mzp.c m4ri/ple.c m4ri/ple_russian.c m4ri/solve.c m4ri/strassen.c m4ri/triangular.c m4ri/triangular_russian.c

all: colswap elimination invert kernel misc multiplication ple smallops solve transpose trsm

compile: tests/test_colswap.c
	gcc -I./m4ri -I. tests/test_colswap.c ${M4RI}

colswap: tests/test_colswap.c
	${SHOW} ${INCLUDES} tests/test_colswap.c ${M4RI}

elimination: tests/test_elimination.c
	${SHOW} ${INCLUDES} tests/test_elimination.c ${M4RI}

invert: tests/test_invert.c
	${SHOW} ${INCLUDES} tests/test_invert.c ${M4RI}

kernel: tests/test_kernel.c
	${SHOW} ${INCLUDES} tests/test_kernel.c ${M4RI}

misc: tests/test_misc.c
	${SHOW} ${INCLUDES} tests/test_misc.c ${M4RI}

multiplication: tests/test_multiplication.c
	${SHOW} ${INCLUDES} tests/test_multiplication.c ${M4RI}

ple: tests/test_ple.c
	${SHOW} ${INCLUDES} tests/test_ple.c ${M4RI}

smallops: tests/test_smallops.c
	${SHOW} ${INCLUDES} tests/test_smallops.c ${M4RI}

solve: tests/test_solve.c
	${SHOW} ${INCLUDES} tests/test_solve.c ${M4RI}

transpose: tests/test_transpose.c
	${SHOW} ${INCLUDES} tests/test_transpose.c ${M4RI}

trsm: tests/test_trsm.c
	${SHOW} ${INCLUDES} tests/test_trsm.c ${M4RI}

clean: 
