CIVL=civl 
DEFINES=-D _OPENMP
INCLUDES=-userIncludePath=./m4ri/ -sysIncludePath=./
SHOW=${CIVL} show ${DEFINES} -ompNoSimplify -ompLoopDecomp=ROUND_ROBIN -inputTHREAD_MAX=3 -enablePrintf=false 
VERIFY=${CIVL} verify -ompNoSimplify -ompLoopDecomp=ROUND_ROBIN -inputTHREAD_MAX=3 -enablePrintf=false 
VERIFYALL=${CIVL} verify -ompNoSimplify -ompLoopDecomp=ALL -inputTHREAD_MAX=3 -enablePrintf=false 
SIMPLIFY=${CIVL} verify -ompLoopDecomp=ALL -inputTHREAD_MAX=3 -enablePrintf=false 

COMMON= ../common/wtime.c ../common/c_timers.c
SOURCE= adc.c dc.c extbuild.c jobcntl.c rbt.c ${COMMON}

all: dc 

dc: 
	${SHOW} ${INCLUDES} ${SOURCE}

clean: 
