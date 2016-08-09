/*
 * Cholesky decomposition;
 * Code from: https://rosettacode.org/wiki/Cholesky_decomposition#C
 */

#include <stdio.h>
#include <stdlib.h>
#include <math.h>

double *cholesky(double *A, int n) {
  double *L = (double*)malloc(n*n*sizeof(double));
  
  for (int i = 0; i < n*n; i++)
    L[i] = 0.0;
  
  for (int i = 0; i < n; i++)
    for (int j = 0; j < (i+1); j++) {
      double sum = 0;
      for (int k = 0; k < j; k++)
	sum += L[i * n + k] * L[j * n + k];
      L[i * n + j] = (i == j) ?
	sqrt(A[i * n + i] - sum) :
	(1.0 / L[j * n + j] * (A[i * n + j] - sum));
    }

  return L;
}

void show_matrix(double *A, int n) {
  for (int i = 0; i < n; i++) {
    for (int j = 0; j < n; j++)
      printf("%f ", A[i * n + j]);
    printf("\n");
  }
}

