/*
 * Self-defined petsc.h header for provesa PETSc examples: ex2a.c, ex2b.c,
 * ex2c.c,ex2d.c. This header is used for verifying the equivalence of those
 * examples by using CIVL. This header is made based on the functions and
 * types which is used in those PETSc examples. The definition of types and 
 * funcitons comes from PETSc home page: https://www.mcs.anl.gov/petsc/
 * PETSc examples: https://repo.anl-external.org/repos/provesa/codes/mxm/
 *
 * Author: Si Li <sili@udel.edu>
 */

#ifndef _PETSC_
#define _PETSC_

#include <math.h>
#define PetscExpScalar(x)     exp(x)

/* -------Types------- */

/* PetscErrorCode - datatype used for return error code from almost
 * all PETSc functions */
typedef int PetscErrorCode;

/* PETSc type that represents a PetscReal.
 * This is the same as a PetscReal except in code that is automatically
 * differentiated it is treated as a constant (not an indendent or 
 * dependent variable) 
 */
typedef double PassiveReal;

/* PETSc type that represents integer - used primarily to represent size
 * of arrays and indexing into arrays. Its size can be * configured with
 * the option-with-64-bit-indices - to be either 
 * 32bit or 64bit [default 32 bit ints]
 */
typedef int PetscInt;

/* PetscReal - PETSc type that represents a real number version of
 * PetscScalar */
typedef double PetscReal;

/* PetscScalar - PETSc type that represents either a double precision
 * real number, a double precision complex number, a single precision
 * real number, a long double or an int - if the code is configured
 * with --with-scalar-type=real, complex --with-precision=single,
 * double,__float128
 */
typedef double PetscScalar;

/* C struct that contains information about a structured grid and
 a processors logical location in it. */
typedef struct DMDALocalInfo { /* using distributed arrays */
  PetscInt dim,dof,sw;
  PetscInt mx,my,mz;    /* global number of grid points in each direction */
  PetscInt xs,ys,zs;    /* starting point of this processor, excluding ghosts */
  PetscInt xm,ym,zm;    /* number of grid points on this processor, excluding ghosts */
  PetscInt gxs,gys,gzs; /* starting point of this processor including ghosts */
  PetscInt gxm,gym,gzm; /* number of grid points on this processor including ghosts */
} DMDALocalInfo;

/* ----------Functions---------- */

/* First executable line of each PETSc function, used for error handling.
 * Final line of PETSc functions should be PetscFunctionReturn(0);
 */
#define PetscFunctionBegin

/* Last executable line of each PETSc function used for error handling.
 * Replaces return() */
#define PetscFunctionReturn(x)    return(x)

/* Adds floating point operations to the global counter. */
PetscErrorCode PetscLogFlops(double ); //{return 0;}

/* Checks error code, if non-zero it calls the error handler and then
 * returns */
PetscErrorCode CHKERRQ(PetscErrorCode ); // {return 0;}

/*
#undef __FUNCT__
#define __FUNCT__ "PetscLogFlops"
PETSC_STATIC_INLINE PetscErrorCode PetscLogFlops(PetscLogDouble n)
{
  PetscFunctionBegin;
#if defined(PETSC_USE_DEBUG)
  if (n < 0) SETERRQ(PETSC_COMM_SELF,PETSC_ERR_ARG_OUTOFRANGE,"Cannot log negative flops");
#endif
  petsc_TotalFlops += PETSC_FLOPS_PER_OP*n;
  PetscFunctionReturn(0);
}
*/

#endif
