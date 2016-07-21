/* PETSc example driver for ex2a.c, ex2b.c,ex2c.c,ex2d.c,
 * https://repo.anl-external.org/repos/provesa/codes/mxm/
 * command: civl verify ex2Driver.c ex2a.c
 */

#include <civlc.cvh>
#include <stdlib.h>
#include "petsc.h"

typedef struct {
   PassiveReal param;          /* test problem parameter */
} AppCtx;

$input int M;
$input int N;
$input PetscScalar x_data[M][N];
PetscScalar f_data[M][N];
$input AppCtx user;
$input DMDALocalInfo info;
$assume(M >=0 && M < info.ys+info.ym);
$assume(N >=0 && N < info.ys+info.ym);

PetscErrorCode FormFunctionLocal(DMDALocalInfo *,PetscScalar **,PetscScalar **,AppCtx *);

int main() {
  PetscScalar **x, **f;

  x = (double **)malloc(M*sizeof(double *));
    for (int i = 0; i < M ; i++) {
      x[i] = (double *)malloc(N*sizeof(double));
      //x[i] = $havoc(&x[i]) 
    }

  f = (double **)malloc(M*sizeof(double *));
    for (int i = 0; i < M ; i++) {
      f[i] = (double *)malloc(N*sizeof(double));
    }

  for (int i = 0; i < M ; i++)
    for (int j = 0; j < N ; j++) {
      x[i][j] = x_data[i][j];
      f[i][j] = f_data[i][j];
    }
  
  FormFunctionLocal(info, x, f, user);
}
