/*
 * Self-defined petsc.h header for provesa examples: ex2a.c, ex2b.c,ex2c.c,ex2d.c.
 * https://repo.anl-external.org/repos/provesa/codes/mxm/
 * Full example from PETSc website: http://www.mcs.anl.gov/petsc/petsc-current/src/snes/examples/tutorials/ex5.c.html
 */

#ifndef _PETSC_
#define _PETSC_

#include <math.h>
#define PetscExpScalar(x)     exp(x)

/* -------Types------- */

/* PetscErrorCode - datatype used for return error code from almost all PETSc functions */
typedef int PetscErrorCode;

/* PETSc type that represents a PetscReal.
 * This is the same as a PetscReal except in code that is automatically differentiated it 
 * is treated as a constant (not an indendent or dependent variable) 
 */
typedef double PassiveReal;

/* PETSc type that represents integer - used primarily to represent size of arrays and indexing
 * into arrays. Its size can be * configured with the option-with-64-bit-indices - to be either 
 * 32bit or 64bit [default 32 bit ints]
 */
typedef int PetscInt;

/* PetscReal - PETSc type that represents a real number version of PetscScalar */
typedef double PetscReal;

/* PetscScalar - PETSc type that represents either a double precision real number, a double precision
 * complex number, a single precision real number, a long double or an int - if the code is configured
 * with --with-scalar-type=real, complex --with-precision=single,double,__float128
 */
typedef double PetscScalar;

/* C struct that contains information about a structured grid and a processors logical location in it. */
typedef struct DMDALocalInfo { /* using distributed arrays */
  PetscInt         dim,dof,sw;
  PetscInt         mx,my,mz;    /* global number of grid points in each direction */
  PetscInt         xs,ys,zs;    /* starting point of this processor, excluding ghosts */
  PetscInt         xm,ym,zm;    /* number of grid points on this processor, excluding ghosts */
  PetscInt         gxs,gys,gzs;    /* starting point of this processor including ghosts */
  PetscInt         gxm,gym,gzm;    /* number of grid points on this processor including ghosts */
} DMDALocalInfo;

/* ----------Functions---------- */

/* First executable line of each PETSc function, used for error handling. Final line of PETSc 
 * functions should be PetscFunctionReturn(0);
 */
#define PetscFunctionBegin

/* Last executable line of each PETSc function used for error handling. Replaces return() */
//void PetscFunctionReturn(0);
#define PetscFunctionReturn(x)    return(x)

/* Adds floating point operations to the global counter. */
PetscErrorCode PetscLogFlops(double ); //{return 0;}

/* Checks error code, if non-zero it calls the error handler and then returns */
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

/******************************************************************************************/
/* about SFI Bratu equation */
/* petsc-2.0.28/src/snes/examples/tutorial/ex5f.F
 *
 *  command: mpirun -np <procs> ex5f [-help] [all PETSc options]
 *  -par <param>： SFI parameter lambda ：0 <= lambda <= 6.81；
    -mx <xg> 
    -my <yg>
    -Nx <npx>
    -Ny <npy>
 */

/*   static char help[] = "Bratu nonlinear PDE in 2d.\n			\
  3: We solve the  Bratu (SFI - solid fuel ignition) problem in a 2D rectangular\n\
  4: domain, using distributed arrays (DMDAs) to partition the parallel grid.\n\
  5: The command line options include:\n\
  6:   -par <parameter>, where <parameter> indicates the problem's nonlinearity\n\
  7:      problem SFI:  <parameter> = Bratu parameter (0 <= par <= 6.81)\n\n\
  8:   -m_par/n_par <parameter>, where <parameter> indicates an integer\n \
  9:       that MMS3 will be evaluated with 2^m_par, 2^n_par";
*/
