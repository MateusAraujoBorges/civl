#include <omp.h>
//#include <stdlib.h>
#include <stdio.h>
#include "headers.h"
#include "par_amg.h"

int
main( int   argc,
      char *argv[] )
{

/*
int hypre_ParCSRMaxEigEstimateCG(hypre_ParCSRMatrix *A,
                                 int scale,
                                 int max_iter,
                                 double *max_eig,
                                 double *min_eig)
*/

   hypre_ParCSRMatrix A;
   int scale = 0;
   int max_iter = 0;
   double max_eig = 0;
   double min_eig = 0;

   int r1 = hypre_ParCSRMaxEigEstimateCG(&A, scale, max_iter, &max_eig, &min_eig);

/*
int hypre_ParCSRRelax_Cheby3(hypre_ParCSRMatrix *A,
                            hypre_ParVector *f,
                            double max_eig,
                            double eig_ratio,
                            int order,
                            hypre_ParVector *u,
                            hypre_ParVector *v,
                            hypre_ParVector *v2)
*/

   hypre_ParVector f;
   double eig_ratio = 0;
   int order = 0;
   hypre_ParVector u;
   hypre_ParVector v;
   hypre_ParVector v2;

/*
   int r2 = hypre_ParCSRRelax_Cheby3(&A, &f, max_eig, eig_ratio, order, &u, &v, &v2);
*/

/*
int hypre_ParCSRRelax_Cheby(hypre_ParCSRMatrix *A,
                            hypre_ParVector *f,
                            double max_eig,
                            double min_eig,
                            double eig_ratio,
                            int order,
                            int scale,
                            int variant,
                            hypre_ParVector *u,
                            hypre_ParVector *v, 
                            hypre_ParVector *r)
*/
   int variant = 0;

   int r2 = hypre_ParCSRRelax_Cheby(&A, &f, max_eig, min_eig, eig_ratio, order, scale, variant, &u, &v, &v2);

}
