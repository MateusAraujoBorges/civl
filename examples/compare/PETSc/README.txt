Example 2:

This is a PETSc example that has been refactored.  This is motivated by some ideas we are exploring in automatic differentiation.  The verification task would be to confirm that all of the variants are equivalent.  They should all be real equivalent (in terms of the function computed -- some of the error checking and flop counting is not the same).  Some of them might even be Herbrand equivalent.

compare two variants:
        civl compare -impl ex2Driver.c ex2a.c -spec ex2Driver.c ex2d.c

compare all variants:
	make

