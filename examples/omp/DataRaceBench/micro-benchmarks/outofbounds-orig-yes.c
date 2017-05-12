/* The outmost loop is parallelized.
   But the inner level loop has out of bound access for b[i][j]
   when j==0. 
   This will case memory access of a previous row's last element.

  For example, an array of 4x4: 
      j=0 1 2 3
   i=0  x x x x
     1  x x x x
     2  x x x x
     3  x x x x
     
    outer loop: i=2, 
    inner loop: j=0
    array element accessed b[i][j-1] becomes b[2][-1], which in turn is b[1][3]
    due to linearized row-major storage of the 2-D array.

    This causes loop-carried data dependence between i=2 and i=1.
*/
#include <stdio.h>
int main(int argc, char* argv[]) 
{
  int i,j;
  int n=100, m=100;
  double b[n][m];
#pragma omp parallel for private(j)
  for (i=0;i<n;i++)
    for (j=0;j<m;j++) // Note there will be out of bound access
      b[i][j]=b[i][j-1];

  printf ("b[50][50]=%f\n",b[50][50]);

  return 0;     
}
  
