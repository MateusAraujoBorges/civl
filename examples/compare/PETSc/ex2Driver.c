/* PETSc example driver for ex2a.c, ex2b.c,ex2c.c,ex2d.c,
 * https://repo.anl-external.org/repos/provesa/codes/mxm/
 */

#include <civlc.cvh>
#include <stdio.h>
#include <stdlib.h>
#include "petsc.h"

typedef struct {
   PassiveReal param;          /* test problem parameter */
} AppCtx;

$input PetscScalar x_data[5][5];
$input PetscScalar f_data[5][5];
$input AppCtx user[5];
$input DMDALocalInfo info[5];

PetscErrorCode FormFunctionLocal(DMDALocalInfo *,PetscScalar **,PetscScalar **,AppCtx *);

int main() {
  PetscScalar **x, **f;

  x = (double **)malloc(5*sizeof(double *));
    for (int i = 0; i < 5 ; i++) {
      x[i] = (double *)malloc(5*sizeof(double));
      //x[i] = $havoc(&x[i]) 
    }

  f = (double **)malloc(5*sizeof(double *));
    for (int i = 0; i < 5 ; i++) {
      f[i] = (double *)malloc(5*sizeof(double));
    }

  for (int i = 0; i < 5 ; i++)
    for (int j = 0; j < 5 ; j++) {
      x[i][j] = x_data[i][j];
      f[i][j] = f_data[i][j];
    }
  
  FormFunctionLocal(info, x, f, user);
}
