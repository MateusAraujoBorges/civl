#include <stdlib.h>

/* = = = = = = = = TASS I/O = = = = = = = = */
#pragma TASS input {N==1}
int N;
#pragma TASS input {M==3}
int M;

#pragma TASS input
double A0[N*M];
#pragma TASS input
double B0[N*M];
#pragma TASS output
double OUTS[N*M];

/* = = = = = = = = Dense Matrix Def = = = = = = = = */
struct DM_struct{
    double * data;
    int num_rows;
    int num_cols;
};

typedef struct DM_struct DenseMatrix;

DenseMatrix * dense_create(int n, int m) {
    DenseMatrix * mat;
    
    mat = (DenseMatrix *) malloc (sizeof(DenseMatrix));
    mat->num_rows = n;
    mat->num_cols = m;
    mat->data = (double*) malloc(n*m*sizeof(double));
    
    return mat;
}

DenseMatrix * hypre_CSRMatrixAdd(DenseMatrix * A, DenseMatrix * B) {
    int i;
    int j;
    int nr;
    int nc;
    double * A_data;
    double * B_data;
    double * C_data;
    DenseMatrix * C;
    
    nr = A->num_rows;
    nc = B->num_cols;
    A_data = A->data;
    B_data = B->data;
    C = dense_create(nr,nc);
    C_data = C->data;
    
#pragma TASS joint invariant LoopCondEquiv 0 <= i && i < nr && 0 <= j && j < nc;
#pragma TASS joint invariant LoopMatAEquiv true;
#pragma TASS joint invariant LoopMatBEquiv true;
#pragma TASS joint invariant LoopMatCEquiv true;
#pragma TASS joint invariant LoopCorrect true;
    for (i=0; i<nr; i++)
        for (j=0; j<nc; j++)
            C_data[i*nc + j] = A_data[i*nc + j] +B_data[i*nc + j];
    return C;
}

void free_dense(DenseMatrix * matrix) {
    free(matrix->data);
    free(matrix);
}

int main() {
    int i;
    DenseMatrix * X;
    DenseMatrix * Y;
    DenseMatrix * Z;
    
    X = dense_create(N,M);
    Y = dense_create(N,M);
    for (i=0; i<N*M; i++)
        X->data[i] = A0[i];
    for (i=0; i<N*M; i++)
        Y->data[i] = B0[i];
    Z = hypre_CSRMatrixAdd(X,Y);
    for (i=0; i<N*M; i++)
        OUTS[i] = Z->data[i];
    free_dense(X);
    free_dense(Y);
    free_dense(Z);
    return 0;
}
