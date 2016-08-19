CIVL = civl
COMPARE = $(CIVL) compare

all: compare_ab compare_ac compare_ad end

compare_ab: ex2Driver.c ex2a.c ex2b.c petsc.c
	$(COMPARE) -impl ex2Driver.c ex2a.c petsc.c -spec ex2Driver.c ex2b.c petsc.c 

compare_ac: ex2Driver.c ex2a.c ex2c.c petsc.c
	$(COMPARE) -impl ex2Driver.c ex2a.c petsc.c -spec ex2Driver.c ex2c.c petsc.c

compare_ad: ex2Driver.c ex2a.c ex2d.c petsc.c
	$(COMPARE) -impl ex2Driver.c ex2a.c petsc.c -spec ex2Driver.c ex2d.c petsc.c

end: 
	@echo Four PETSc variants are equivalent!
	
clean: 
	rm -f *~
	rm -f -r CIVLREP
