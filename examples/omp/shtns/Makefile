CIVL=civl
INCLUDES=-userIncludePath=./
SHOW=${CIVL} show -ompNoSimplify -ompLoopDecomp=ROUND_ROBIN -inputTHREAD_MAX=3 -enablePrintf=false 
VERIFY=${CIVL} verify -ompNoSimplify -ompLoopDecomp=ROUND_ROBIN -inputTHREAD_MAX=3 -enablePrintf=false 
VERIFYALL=${CIVL} verify -ompNoSimplify -ompLoopDecomp=ALL -inputTHREAD_MAX=3 -enablePrintf=false 
SIMPLIFY=${CIVL} verify -ompLoopDecomp=ALL -inputTHREAD_MAX=3 -enablePrintf=false 

SOURCE= sht_com.c sht_dct.c sht_fly.c sht_func.c sht_init.c sht_legendre.c sht_mem.c sht_mic.c sht_omp.c 

all: time_SHT

time_SHT: time_SHT.c
	${SHOW} ${INCLUDES} time_SHT.c ${SOURCE}

clean: 
