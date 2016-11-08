#include <stdlib.h>

/* = = = = = = = = TASS I/O = = = = = = = = */
#pragma TASS input {N==1}
int N;
#pragma TASS input {M==4}
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

DenseMatrix * dense_add(DenseMatrix * X, DenseMatrix * Y) {
  int i;
  int j;
  int n;
  int m;
  DenseMatrix * R;

  n = X->num_rows;
  m = X->num_cols;
  R = dense_create(n,m);
  
addLoop:
  for (i=0; i<n; i++)
    for (j=0; j<m; j++)
      R->data[i*m + j] = X->data[i*m + j] + Y->data[i*m + j];
  return R;
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
  Z = dense_add(X,Y);
  for (i=0; i<N*M; i++)
    OUTS[i] = Z->data[i];
  free_dense(X);
  free_dense(Y);
  free_dense(Z);
  return 0;
}
