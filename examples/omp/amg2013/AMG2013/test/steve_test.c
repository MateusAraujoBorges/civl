//
//  steve_test.c
//  
//
//  Created by siegel on 10/13/16.
//
//

// #include "parcsr_ls.h"
#include "parcsr_mv.h"

int main() {
    // hypre_ParCSRMatrix A;
    // double scnorm;
    // int hypre_ParCSRMatrixScaledNorm ( hypre_ParCSRMatrix *A , double *scnorm );
    // int n = hypre_ParCSRMatrixScaledNorm(&A, &scnorm);
    
    //double hypre_ParVectorInnerProd( hypre_ParVector *x, hypre_ParVector *y )
    hypre_ParVector x, y;
    double result = hypre_ParVectorInnerProd(&x, &y);
    return result != 0;
}
