/************************************************************
 * cholesky.c  main program for testing Cholesky            *
 * decomposition routine cholesky()                         *
 *                                                          *
 * Created by William J. De Meo                             *
 * on 11/29/97                                              *
 *                                                          *
 * http://www.math.hawaii.edu/~williamdemeo/C/stat243/reports/hw3/hw3/node6.html
 ************************************************************/
#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include "prototypes.h"
#define MAX_NAME 100

void cholesky(long N, double *A, double *diag);
void read_name(char *);

int main()
{
     char *filename;
     double *A, *diag;
     long i, j, dim;
  
     filename = cmalloc(MAX_NAME);

     printf("\nEnter file name containing the spd matrix: ");
     read_name(filename);
     printf("\nEnter its dimension: ");
     scanf("%d",&dim);

     A = dmalloc(dim*dim);
     diag = dmalloc(dim);
  
     matlabread(A, dim, dim, filename); 
     /*matrix is stored contiguously column-wise */

     cholesky(dim,A,diag);
     
     printf("\nThe Cholesky factor is: \nL = \n");
     for(i=0;i<dim;i++)
     {
          for(j=0;j<i;j++)
               printf("%4.5lf \t", A[dim*j+i]);
          printf("%4.5lf", diag[i]);
          printf("\n");
     }
         
}
  
void read_name(char *name)
{
     int c, i = 0;
  
     while ((c = getchar()) != EOF && c != ' ' && c != '\n')
          name[i++] = c;
     name[i] = '\0';
}

/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  cholesky.c

  Created on 11/29/97 by William J. De Meo

  Purpose: Cholesky decomposition of an n-by-n spd matrix 
           
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*

/* Subroutine cholesky:

   Arguments: 
              N  dimension of A

              A 
                 on entry: the N by N matrix to be decomposed
                 on exit: upper triangle is still A
                          lower sub-triangle is the sub-trangle
                          of the Cholesky factor L

              diag 
                 on entry: an arbitrary vector of length N
                 on exit: the diagonal of the Cholesky factor L

*/

void cholesky(long N, double *A, double *diag)
{
     long i,j,k;
     for(j=0;j<N;j++)
          diag[j] = A[N*j+j];
     for(j=0;j<N;j++)
     {
          for(k=0;k<j;k++)
               diag[j] -= A[N*k+j]*A[N*k+j];
          diag[j] = sqrt(diag[j]);
          for(i=j+1;i<N;i++)
          {
               for(k=0;k<j;k++)
                    A[N*j+i] -= A[N*k+i]*A[N*k+j];
               A[N*j+i]/=diag[j];
          }
     }
}
