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

$input int M = 5;
$input int N = 5;
//$assume(M>=0 && M < 5);
//$assume(N>=0 && N < 5);
$input PetscScalar x_data[M][N];
$output PetscScalar f_data[M][N];
$input AppCtx user;
$input DMDALocalInfo info;
$assume(info.ys >=0 && info.ys+info.ym < M);
$assume(info.xs >=0 && info.xs+info.xm < N);

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
    }
  
  FormFunctionLocal(&info, x, f, &user);

  for (int i = 0; i < M ; i++)
    for (int j = 0; j < N ; j++) {
      f_data[i][j] = f[i][j];
    }

  for(int i = 0; i< M; i++) {
    free(x[i]);
    free(f[i]);
  }
  free(x);
  free(f);  
}
