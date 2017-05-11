/* A kernel for two level parallelizable loop with reduction 
 if reduction(error) is missing, there is race condition.
*/
#include <stdio.h>
int main(int argc, char* argv[])
{
  int i,j;
  float temp, error;
  int len=100;

   float u[100][100];
#pragma omp parallel for private (temp,i,j)
  for (i = 0; i < len; i++)
    for (j = 0; j < len; j++)
    {
      temp = u[i][j];
      error = error + temp * temp;
    }
  printf ("error = %f\n", error);  
  return 0;
}
