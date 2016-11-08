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

/* = = = = = = = = Dense and CSR Matrix Def = = = = = = = = */
struct CSRM_struct {
    double  *data;
    int     *i;
    int     *j;
    int      num_rows;
    int      num_cols;
    int      num_nonzeros;
};

typedef struct CSRM_struct hypre_CSRMatrix;

/* = = = = = = = = Hypre_CSR = = = = = = = = */
hypre_CSRMatrix *
hypre_CSRMatrixCreate(
                      int num_rows,
                      int num_cols,
                      int num_nonzeros )
{
    hypre_CSRMatrix  *matrix;
    
    matrix = (hypre_CSRMatrix *) malloc (sizeof(hypre_CSRMatrix));
    matrix->data = (double *) NULL;
    matrix->i = (int *) NULL;
    matrix->j = (int *) NULL;
    matrix->num_rows = num_rows;
    matrix->num_cols = num_cols;
    matrix->num_nonzeros = num_nonzeros;
    
    return matrix;
}


int
hypre_CSRMatrixInitialize(
                          hypre_CSRMatrix *matrix )
{
    int num_rows;
    int num_nonzeros;
    int ierr;
    
    ierr = 0;
    num_rows = matrix->num_rows;
    num_nonzeros = matrix->num_nonzeros;
    
    if (matrix->data == (double *)NULL && num_nonzeros != 0 )
        matrix->data = (double *)malloc(num_nonzeros*sizeof(double));
    if (matrix->i == (int *)NULL)
        matrix->i = (int *)malloc((num_rows + 1)*sizeof(int));
    if (matrix->j == (int *)NULL)
        matrix->j = (int *)malloc(num_nonzeros*sizeof(int));
    return ierr;
}

void free_CSR( hypre_CSRMatrix *matrix ) {
    if (matrix->data != (double *) NULL)
        free(matrix->data);
    if (matrix->i != (int *) NULL)
        free(matrix->i);
    if (matrix->j != (int *) NULL)
        free(matrix->j);
    free(matrix);
}

hypre_CSRMatrix *
hypre_CSRMatrixAdd( hypre_CSRMatrix *A, hypre_CSRMatrix *B) {
    double * A_data;
    int * A_i;
    int * A_j;
    int nrows_A;
    int ncols_A;
    double * B_data;
    int * B_i;
    int * B_j;
    int nrows_B;
    int ncols_B;
    hypre_CSRMatrix *C;
    double *C_data;
    int *C_i;
    int *C_j;
    int ia;
    int ib;
    int ic;
    int jcol;
    int num_nonzeros;
    int pos;
    int * marker;
    
    A_data = A->data;
    A_i = A->i;
    A_j = A->j;
    nrows_A = A->num_rows;
    ncols_A = A->num_cols;
    B_data = B->data;
    B_i = B->i;
    B_j = B->j;
    nrows_B = B->num_rows;
    ncols_B = B->num_cols;
    
    marker = (int *) malloc (ncols_A * sizeof(int));
    C_i = (int *) malloc ((nrows_A+1) * sizeof(int));
    for (ia = 0; ia < ncols_A; ia++)
        marker[ia] = -1;
    num_nonzeros = 0;
    C_i[0] = 0;
    for (ic = 0; ic < nrows_A; ic++) {
        for (ia = A_i[ic]; ia < A_i[ic+1]; ia++) {
            jcol = A_j[ia];
            marker[jcol] = ic;
            num_nonzeros++;
        }
        for (ib = B_i[ic]; ib < B_i[ic+1]; ib++) {
            jcol = B_j[ib];
            if (marker[jcol] != ic) {
                marker[jcol] = ic;
                num_nonzeros++;
            }
        }
        C_i[ic+1] = num_nonzeros;
    }
    
    C = hypre_CSRMatrixCreate(nrows_A, ncols_A, num_nonzeros);
    C->i = C_i;
    hypre_CSRMatrixInitialize(C);
    C_j = C->j;
    C_data = C->data;
    
    for (ia = 0; ia < ncols_A; ia++)
        marker[ia] = -1;
    pos = 0;
    
#pragma TASS invariant LoopNNZ pos >= A_i[ic] && pos >= B_i[ic] && pos <= A_i[ic] + B_i[ic];
#pragma TASS joint invariant LoopCondEquiv ic == spec.i && nrows_A == spec.nr && ncols_A == spec.nc;
#pragma TASS joint invariant LoopMatAEquiv (forall {int xa | A_i[ic]<=xa && xa<A_i[ic+1]} (spec.j != A_j[xa] || spec.A_data[ic*ncols_A + spec.j] == A_data[xa]));
#pragma TASS joint invariant LoopMatBEquiv (forall {int xb | B_i[ic]<=xb && xb<B_i[ic+1]} (spec.j != B_j[xb] || spec.B_data[ic*ncols_A + spec.j] == B_data[xb]));
#pragma TASS joint invariant LoopMatCEquiv (forall {int xc | C_i[ic]<=xc && xc<C_i[ic+1]} (spec.j != C_j[xc] || spec.C_data[ic*ncols_A + spec.j] == C_data[xc]));
#pragma TASS joint invariant LoopCorrect (forall {int r | 0 <= r && r < spec.nr}(forall {int c | 0 <= c && c < spec.nc} (((forall {int nz1 | C_i[r] <= nz1 && nz1 < C_i[r+1]} (c != C_j[nz1] || spec.C_data[r*spec.nc + c] != C_data[nz1])) != true) || (forall {int nz2 | C_i[r] <= nz2 && nz2 < C_i[r+1]} (c != C_j[nz2] || spec.C_data[r*spec.nc + c] != 0.0)))));
    for (ic = 0; ic < nrows_A; ic++) {
        for (ia = A_i[ic]; ia < A_i[ic+1]; ia++) {
            jcol = A_j[ia];
            C_j[pos] = jcol;
            C_data[pos] = A_data[ia];
            marker[jcol] = pos;
            pos++;
        }
        for (ib = B_i[ic]; ib < B_i[ic+1]; ib++) {
            jcol = B_j[ib];
            if (marker[jcol] < C_i[ic]) {
                C_j[pos] = jcol;
                C_data[pos] = B_data[ib];
                marker[jcol] = pos;
                pos++;
            }else{
                C_data[marker[jcol]] += B_data[ib];
            }
        }
    }
    free(marker);
    return C;
}

double *
expand(hypre_CSRMatrix * mat)
{
    int i;
    int j;
    int k;
    double * rtn;
    
    rtn = (double *) malloc ((mat->num_rows) * (mat->num_cols) * sizeof(double));
    for (i = 0; i < mat->num_rows;i++)
        for (j = 0; j < mat->num_cols; j++)
            rtn[i*M + j] = 0.0;
    k = 0;
    for (i = 0; i < mat->num_rows; i++)
        while(k < mat->i[i+1])
            for (j = 0; (k < mat->num_nonzeros) && (j < mat->num_cols); j++)
                if (j == mat->j[k]){
                    rtn[i*M + j] = mat->data[k];
                    k++;
                }
    
    return rtn;
}

int main() {
    int i;
    int j;
    int k;
    int xnz;
    int ynz;
    double tmp;
    double * sum;
    hypre_CSRMatrix * X;
    hypre_CSRMatrix * Y;
    hypre_CSRMatrix * Z;
    
    xnz = 0;
    for (i=0; i < N*M; i++)
        if (A0[i] != 0)
            xnz = xnz + 1;
    ynz = 0;
    for (i=0; i < N*M; i++)
        if (B0[i] != 0)
            ynz = ynz + 1;
    X = hypre_CSRMatrixCreate(N,M, xnz);
    Y = hypre_CSRMatrixCreate(N,M, ynz);
    hypre_CSRMatrixInitialize(X);
    hypre_CSRMatrixInitialize(Y);
    k = 0;
    X->i[0] = k;
    for (i = 0; i < N; i++){
        for (j = 0; j < M; j++){
            tmp = A0[i*M + j];
            if (tmp != 0){
                X->data[k] = tmp;
                X->j[k] = j;
                k++;
            }
        }
        X->i[i+1] = k;
    }
    k = 0;
    Y->i[0] = k;
    for (i = 0; i < N; i++){
        for (j = 0; j < M; j++){
            tmp = B0[i*M + j];
            if (tmp != 0){
                Y->data[k] = tmp;
                Y->j[k] = j;
                k++;
            }
        }
        Y->i[i+1] = k;
    }
    Z = hypre_CSRMatrixAdd(X,Y);
    sum = expand(Z);
    for (i=0; i<N*M; i++)
        OUTS[i] = sum[i];
    free_CSR(X);
    free_CSR(Y);
    free_CSR(Z);
    free(sum);
    return 0;
}
