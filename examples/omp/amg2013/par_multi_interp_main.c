#include <stdlib.h>
#include <stdio.h>
#include <math.h>

#include "krylov.h"
#include "sstruct_mv.h"

int
main( int   argc,
      char *argv[] )
{
   HYPRE_ParCSRMatrix    par_A;
   HYPRE_ParCSRMatrix    par_S;

int r = hypre_BoomerAMGBuildMultipass(hypre_ParCSRMatrix  *A,
                   int                 *CF_marker,
                   hypre_ParCSRMatrix  *S,
                   HYPRE_BigInt        *num_cpts_global,
                   int                  num_functions,
                   int                 *dof_func,
                   int                  debug_flag,
                   double               trunc_factor,
                   int		 	P_max_elmts,
                   int                  weight_option,
                   int                 *col_offd_S_to_A,
                   hypre_ParCSRMatrix **P_ptr );

}
