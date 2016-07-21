CIVL = civl
COMPARE = $(CIVL) compare

all: compare_ab compare_ac compare_ad end

compare_ab: ex2Driver.c ex2a.c ex2b.c
	$(COMPARE) -impl ex2Driver.c ex2a.c -spec ex2Driver.c ex2b.c 

compare_ac: ex2Driver.c ex2a.c ex2c.c
	$(COMPARE) -impl ex2Driver.c ex2a.c -spec ex2Driver.c ex2c.c 

compare_ad: ex2Driver.c ex2a.c ex2d.c
	$(COMPARE) -impl ex2Driver.c ex2a.c -spec ex2Driver.c ex2d.c 

end: 
	@echo Four PETSc variants are equivalent!
	
clean: 
	rm -f *~
	rm -f -r CIVLREP
