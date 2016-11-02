
#include <stdlib.h>

// Dense matrix spec...

#pragma TASS input {N==3}
int N;
#pragma TASS input {M==3}
int M;

#pragma TASS input
double A0[N*M];
#pragma TASS input
double B0[N*M];
#pragma TASS output
double C_OUT[N*M];

/*
struct DM_struct {
  double * data;
  int num_rows;
  int num_cols;
};
*/

typedef double DenseMatrix;

//typedef struct DM_struct DenseMatrix;
//typedef DenseMatrix * DM;


double * dense_create(int n, int m) {
  double * mat;

  mat = (double*)malloc(n*m*sizeof(double));
  /*
  mat->num_rows = n;
  mat->num_cols = m;
  mat->data = (double*) malloc(n*m*sizeof(double));
  */
  return mat;
}


DenseMatrix * dense_add(int n, int m, DenseMatrix *A, DenseMatrix *B) {
  int i;
  DenseMatrix * C;

  C = dense_create(n,m);
  for (i=0; i<n*m; i++)
    C[i] = A[i] + B[i];
  return C;
}

void free_dense(DenseMatrix *matrix) {
  //free(matrix->data);
  free(matrix);
}

int main() {
  int i;
  DenseMatrix * C;

  C = dense_add(N,M,&A0[0],&B0[0]);
  for (i=0; i<N*M; i++)
    C_OUT[i] = C[i];
  free_dense(C);
  return 0;
}
