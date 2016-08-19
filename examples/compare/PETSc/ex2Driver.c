/* PETSc examples driver for ex2a.c, ex2b.c,ex2c.c,ex2d.c,
 * https://repo.anl-external.org/repos/provesa/codes/mxm/
 * simple examples run command: civl verify ex2Driver.c ex2a.c
 * compare all examples command: make
 */

#include <civlc.cvh>
#include <stdlib.h>
#include "petsc.h"

typedef struct {
   PassiveReal param;          /* test problem parameter */
} AppCtx;

$input int M;
$input int N;
$assume(1 < M && M <= 4);
$assume(1 < N && N <= 4);
$input double x_data[M][N];

//TypeAnalyzer Exception if we define $input AppCtx user;
AppCtx user;
$input double user2;
user.param = user2;

$input int xs, ys, xm, ym;
DMDALocalInfo info;
info.xs = xs;
info.ys = ys;
info.xm = xm;
info.ym = ym;
info.mx = N;
info.my = M;

$assume(ys >= 0 && ym >0 && ys+ym <= M);
$assume(xs >= 0 && xm >0 && xs+xm <= N);

$output double f_data[ym][xm];

PetscErrorCode FormFunctionLocal(DMDALocalInfo *,PetscScalar **,PetscScalar **,AppCtx *);

int main() {
  PetscScalar **x, **f;

  x = (double **)malloc(M*sizeof(double *));
    for (int i = 0; i < M ; i++) {
      x[i] = (double *)malloc(N*sizeof(double));
    }

  f = (double **)malloc(M*sizeof(double *));
    for (int i = 0; i < M ; i++) {
      f[i] = (double *)malloc(N*sizeof(double));
    }

  for (int i = 0; i < M ; i++)
    for (int j = 0; j < N ; j++) {
      x[i][j] = x_data[i][j];
    }

  $elaborate(info.xs);
  $elaborate(info.ys);

  FormFunctionLocal(&info, x, f, &user);

  // store the portion of array to f_data
  for (int i = 0; i < info.ym ; i++)
    for (int j = 0; j < info.xm ; j++) {
      f_data[i][j] = f[info.ys+i][info.xs+j];
    }
    
  for (int i = 0; i< M; i++) {
    free(x[i]);
    free(f[i]);
  }
  free(x);
  free(f);  
}
