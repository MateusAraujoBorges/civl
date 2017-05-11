// Some threads may finish the for loop early and execute errors = dt[9]+1
// while another thread may still be simultaneously executing
//  the for worksharing region by writing to d[9], 
// which may cause a data race.
//  This is a good test for dynamic tools since the data race does not always happen at runtime. 
//
// Liao, source paper: Ma Symbolic Analysis of Concurrency Errors in OpenMP Programs, ICPP 2013
#include <stdio.h>
#include <assert.h>

int main()
{
  int i,error;
  int len = 1000;
  int a[1000], b=5;

  for (i=0; i<len; i++)
    a[i]= i;
 
#pragma omp parallel shared(b, error) 
  {
#pragma omp for nowait
    for(i = 0; i < len; i++)
      a[i] = b + a[i]*5;

#pragma omp single
    error = a[9] + 1;
  }

  printf ("error = %d\n", error);
//  assert (error==51); 
  return 0;
}  
