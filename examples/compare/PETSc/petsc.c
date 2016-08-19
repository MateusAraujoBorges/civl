/* This file completes the definitions of some functions
 * which are declared in petsc.h.
 */
#include "petsc.h"


/* Adds floating point operations to the global counter. */
PetscErrorCode PetscLogFlops(double ) {return 0;}

/* Checks error code, if non-zero it calls the error handler and then
 * returns */
PetscErrorCode CHKERRQ(PetscErrorCode ) {return 0;}
