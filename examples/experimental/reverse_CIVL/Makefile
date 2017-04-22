CIVL=/Users/snarayan/Software/CIVL-1.7.1_3357/bin/civl
VERIFY=${CIVL} verify
COMPARE=${CIVL} compare
REPLAY=${CIVL} replay
MYDIR=.
DENSE_REVERSE_DEFINE = -DADIC_DENSE_REVERSE


#all: compare
all: civl adic_out

#compare: compare1 compare2

#civl: hand_CIVL adic_CIVL compare_CIVL compareG_CIVL compareGV_CIVL
civl: adic_CIVL 

hand_CIVL: driver.c hand_driver.c
	${VERIFY} driver.c hand_driver.c

adic_CIVL: driver.c adic_driver.c runtime_dense_reverse/ad_grad.c runtime_dense_reverse/ad_tape.c runtime_dense_reverse/ad_rev.c head.cn.xb.pp.c
	${VERIFY} ${DENSE_REVERSE_DEFINE} -userIncludePath=${MYDIR}:${MYDIR}/runtime_dense_reverse/ driver.c runtime_dense_reverse/ad_grad.c runtime_dense_reverse/ad_tape.c runtime_dense_reverse/ad_rev.c adic_driver.c head.cn.xb.pp.c

tap_CIVL: driver.c tap_driver.c o_fcn_bv.c
	${VERIFY} driver.c tap_driver.c o_fcn_bv.c

#compare1: driver.c hand_driver.c adic_driver.c
#	${COMPARE} -min -enablePrintf=false -impl driver.c hand_driver.c -spec ${DENSE_REVERSE_DEFINE} -userIncludePath=${MYDIR}:${MYDIR}/runtime_dense_reverse/ driver.c adic_driver.c runtime_dense_reverse/ad_grad.c head.cn.xb.pp.c
#	${REPLAY} -enablePrintf=false -showTransitions -impl driver.c hand_driver.c -spec driver.c adic_driver.c runtime_dense_reverse/ad_grad.c head.cn.xb.pp.c

#compare2: driver.c hand_driver.c adic_driver.c
#	${COMPARE} -impl -D_gAssumption driver.c hand_driver.c -spec ${DENSE_REVERSE_DEFINE} -userIncludePath=${MYDIR}:${MYDIR}/runtime_dense_reverse/ driver.c adic_driver.c runtime_dense_reverse/ad_grad.c head.cn.xb.pp.c

#compareGV_CIVL: driver.c hand_driver.c adic_driver.c
#	${COMPARE} -spec -D_gAssumption driver.c hand_driver.c -impl ${DENSE_REVERSE_DEFINE} -userIncludePath=${MYDIR}:${MYDIR}/runtime_dense_reverse/ driver.c adic_driver.c runtime_dense_reverse/ad_grad.c head.cn.xb.pp.c

#compare3: driver.c hand_driver.c tap_driver.c
#	${COMPARE} -spec -D_gAssumption driver.c hand_driver.c -impl driver.c tap_driver.c head_d.c

tap_out: driver.c tap_driver.c o_fcn_bv.c
	gcc driver.c tap_driver.c o_fcn_bv.c -lm -o tap_out

tap_out_sw: driver_sw.c tap_driver.c o_fcn_bv.c
	gcc driver_sw.c tap_driver.c o_fcn_bv.c -lm -o rtap_out

compare4: driver.c tap_driver.c adic_driver.c o_fcn_bv.c adic_driver.c runtime_dense_reverse/ad_grad.c runtime_dense_reverse/ad_tape.c runtime_dense_reverse/ad_rev.c head.cn.xb.pp.c
	${COMPARE} -spec -D_gAssumption driver.c tap_driver.c o_fcn_bv.c -impl ${DENSE_REVERSE_DEFINE} -userIncludePath=${MYDIR}:${MYDIR}/runtime_dense_reverse/ driver.c runtime_dense_reverse/ad_grad.c runtime_dense_reverse/ad_tape.c runtime_dense_reverse/ad_rev.c adic_driver.c head.cn.xb.pp.c

adic_out: driver.c adic_driver.c runtime_dense_reverse/ad_grad.c runtime_dense_reverse/ad_tape.c runtime_dense_reverse/ad_rev.c head.cn.xb.pp.c
	gcc -g ${DENSE_REVERSE_DEFINE} -Iruntime_dense_reverse driver.c adic_driver.c runtime_dense_reverse/ad_grad.c runtime_dense_reverse/ad_tape.c runtime_dense_reverse/ad_rev.c head.cn.xb.pp.c -lm -o adic_out

adic_out_sw: driver_sw.c adic_driver.c runtime_dense_reverse/ad_grad.c runtime_dense_reverse/ad_tape.c runtime_dense_reverse/ad_rev.c head.cn.xb.pp.c
	gcc -g ${DENSE_REVERSE_DEFINE} -Iruntime_dense_reverse driver_sw.c adic_driver.c runtime_dense_reverse/ad_grad.c runtime_dense_reverse/ad_tape.c runtime_dense_reverse/ad_rev.c head.cn.xb.pp.c -lm -o radic_out


clean:
	rm -f -r CIVLREP adic_out
	rm -Rf -f *~ hand_out tap_out *.o *.lo *.libs *.la
