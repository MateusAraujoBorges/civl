#the cg3 cases are under developing, they keep running...

CIVL=civl
VERIFY=${CIVL} verify -checkDivisionByZero=false 

cg5_prob: cg.cvl
	${VERIFY} -prob cg.cvl 

cg2_cholesky: cg2_cholesky.cvl
	${VERIFY}  cg2_cholesky.cvl

cg2_sylvester: cg2_sylvester.cvl
	${VERIFY} cg2_sylvester.cvl

cg2: cg2.cvl
	${VERIFY} cg2.cvl

clean: 
	rm -f -r CIVLREP
	rm -r -f *~
