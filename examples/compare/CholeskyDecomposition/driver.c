/*
 * Driver to verify the correctness of Cholesky decomposition 
 * function by CIVL.
 * Command: civl verify -checkDivisionByZero=false driver.c cholesky2.c 
 * Author: Si Li (sili@udel.edu)
 */

#include <civlc.cvh>
#include <stdlib.h>
#include <stdio.h>

$input int n = 3;
$input double diag1,diag2,diag3,off1,off2,off3;
//$input double a1, a2, a3;

double *cholesky(double *, int );
void show_matrix(double *, int );
void showTranspose(double *A, int n, double (*B)[n]);

int main () {  
  //  double A[] = {a1, a2,  
  //            a2, a3};
  double A[] = {diag1, off1, off2,
		off1, diag1, off3,
                off2, off3,  diag1};
  double B[n][n]; 
  double BT[n][n];
  double C[n][n];
  
  double *factor = cholesky(A, n);

  printf("\nThe factor is:\n");
  show_matrix(factor, n);

  printf("\nThe transpose of factor is:\n");
  showTranspose(factor, n, B);

  for (int i = 0; i < n; i++)
    for (int j = 0; j < n; j++)
      BT[i][j] = B[j][i];

  //calculate factor multiply its transpose
  for (int i = 0; i < n; i++)
    for (int j = 0; j < n; j++) {
      C[i][j] = 0.0;
      for (int k =0; k < n; k++)
	C[i][j] += B[i][k]*BT[k][j];
    }

  // check if factor is correct
  for (int i = 0; i < n; i++)
    for (int j = 0; j < n; j++)
      $assert(C[i][j] == A[i * n + j]);
  
  free(factor);
  return 0;
}

void showTranspose(double *A, int n, double (*B)[n])
{
  for (int i = 0; i < n; i++) {
    for (int j = 0; j < n; j++) {
      B[i][j] = A[i * n + j];
    }
  }

  for (int i = 0; i < n; i++) {
    for (int j = 0; j < n; j++)
      printf("%f ", B[j][i]);
    printf("\n");
  }
}

