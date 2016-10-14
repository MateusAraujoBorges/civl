//
//  steve_test.c
//  
//
//  Created by siegel on 10/13/16.
//
//

#include "parcsr_ls.h"

int main() {
    hypre_ParCSRMatrix A;
    double scnorm;
    // int hypre_ParCSRMatrixScaledNorm ( hypre_ParCSRMatrix *A , double *scnorm );
    int n = hypre_ParCSRMatrixScaledNorm(&A, &scnorm);
    return n;
}
