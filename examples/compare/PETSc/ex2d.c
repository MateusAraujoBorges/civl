/* ------------------------------------------------------------------------

    Solid Fuel Ignition (SFI) problem.  This problem is modeled by
    the partial differential equation
  
            -Laplacian u - lambda*exp(u) = 0,  0 < x,y < 1,
  
    with boundary conditions
   
             u = 0  for  x = 0, x = 1, y = 0, y = 1.
  
    A finite difference approximation with the usual 5-point stencil
    is used to discretize the boundary value problem to obtain a nonlinear 
    system of equations.
  ------------------------------------------------------------------------- */

#include <petscdmda.h>
#include <petscsnes.h>

typedef struct {
   PassiveReal param;          /* test problem parameter */
} AppCtx;

/* ------------------------------------------------------------------- */
#undef __FUNCT__
#define __FUNCT__ "FormFunctionLocal"
/* 
   FormFunctionLocal - Evaluates nonlinear function, F(x) on local process patch
 */
PetscErrorCode FormFunctionLocal(DMDALocalInfo *info,PetscScalar **x,PetscScalar **f,AppCtx *user)
{
  PetscErrorCode ierr;
  PetscInt       i,j;
  PetscReal      lambda,hx,hy,hxdhy,hydhx,sc;
  PetscScalar    u,uxx,uyy;

  PetscFunctionBegin;

  lambda = user->param;
  hx     = 1.0/(PetscReal)(info->mx-1);
  hy     = 1.0/(PetscReal)(info->my-1);
  sc     = hx*hy*lambda;
  hxdhy  = hx/hy;
  hydhx  = hy/hx;

  /*
     Compute function over the locally owned part of the grid
  */
  for (j=info->ys; j<info->ys+info->ym; j++) {
    for (i=info->xs; i<info->xs+info->xm; i++) {
      if (i == 0 || j == 0 || i == info->mx-1 || j == info->my-1) {
        f[j][i] = 2.0*(hydhx+hxdhy)*x[j][i];
        ierr = PetscLogFlops(3.0);CHKERRQ(ierr);
      } else {
        f[j][i] = FormFunctionPt(x[j][i],x[j-1][i],x[j+1][i],x[j][i-1],x[j][i+1],hxdhy,hyhdx,sc)
        ierr = PetscLogFlops(11.0);CHKERRQ(ierr);
      }
    }
  }
  PetscFunctionReturn(0);
}

PetscScalar FormFunctionPt(PetscScalar C,PetscScalar S,PetscScalar N,PetscScalar W,PetscScalar E,PetscReal hxdhy,PetscReal hydhx,PetscReal sc) {
      PetscScalar    f;

      f = FormFunctionLin(C,S,N,W,E,hxdhy,hyhdx,sc);
      f += FormFunctionNonlin(C,S,N,W,E,hxdhy,hyhdx,sc);

      return f;
}

PetscScalar FormFunctionLin(PetscScalar C,PetscScalar S,PetscScalar N,PetscScalar W,PetscScalar E,PetscReal hxdhy,PetscReal hydhx,PetscReal sc) {
      PetscScalar    uxx,uyy;

      uxx     = (- W - E)*hydhx;
      uyy     = (- S - N)*hxdhy;
      return (uxx + uyy);
}

PetscScalar FormFunctionNonlin(PetscScalar C,PetscScalar S,PetscScalar N,PetscScalar W,PetscScalar E,PetscReal hxdhy,PetscReal hydhx,PetscReal sc) {
      PetscScalar    uxx,uyy;

      uxx     = (2.0*C)*hydhx;
      uyy     = (2.0*C)*hxdhy;
      return (uxx + uyy + sc*PetscExpScalar(C));
}
