/* ************************************************************
 * matmat_spec.c : sequential multiplication of two matrices.
 *
 * To execute: cc matmat_mw.c ; ./a.out N L M 
 *  
 * Arguments N L M should be replaced with any integer numbers which
 * is no larger than the corresponding dimension decided in the "data"
 * file.
 *
 * To verify: civl verify matmat_spec.c
 *
 * From FEVS.
 * ************************************************************
 */
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#ifdef _CIVL

#include <civlc.cvh>
/* Dimensions of 2 matrices: a[N][L] * b[L][M] */
$input int NB = 3;      // upper bound of N
$input int N;
$assume(0 < N && N <= NB);
$input int LB = 3;      // upper bound of L
$input int L;
$assume(0 < L && L <= LB);
$input int MB = 3;      // upper bound of M
$input int M;
$assume(0 < M && M <= MB);
$input double a[N][L];  // input data for matrix a
$input double b[L][M];  // input data for matrix b
$output double output[N][M];

#else

FILE * fp;              // pointer to the data file which gives two matrices
int N, L, M;

#endif

/* prints a matrix. In CIVL mode, it will compare the matrix with the
   result of the sequential run.*/
void printMatrix(int numRows, int numCols, double *m) {
  int i, j;

  for (i = 0; i < numRows; i++) {
    for (j = 0; j < numCols; j++) 
      printf("%f ", m[i*numCols + j]);
    printf("\n");
  }
  printf("\n");
}

/* Computes a vetor with length L times a matrix with dimensions [L][M] */
void vecmat(double vector[L], double matrix[L][M], double result[M]) {
  int j, k;

  for (j = 0; j < M; j++)
    for (k = 0, result[j] = 0.0; k < L; k++)
      result[j] += vector[k]*matrix[k][j];
}

int main(int argc, char *argv[]) {
  int i, j;

#ifndef _CIVL
  if(argc != 3) {
    printf("Please specify values for N, L, M.\n");
    exit(0);
  }
  N = atoi(argv[1]);
  L = atoi(argv[2]);
  M = atoi(argv[3]);
#endif

  double c[N][M];

#ifndef _CIVL
  double a[N][L], b[L][M];

  fp = fopen("data", "r");
  for (i = 0; i < N; i++)
    for (j = 0; j < L; j++)
      fscanf(fp,"%lf", &a[i][j]);
  for (i = 0; i < L; i++)
    for (j = 0; j < M; j++)
      fscanf(fp,"%lf",&b[i][j]);
  fclose(fp);
#endif
  for(int i=0; i < N; i++)
    vecmat(a[i], b, &c[i][0]);
#ifdef _CIVL
  $elaborate(N*L*M);
  // copy to out put
  for(int i=0; i < N; i++)
    memcpy(output[i], c[i], M * sizeof(double));
#endif
  printMatrix(N, M, &c[0][0]);
  return 0;
}

