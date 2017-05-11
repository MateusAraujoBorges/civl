// This x should be not lastprivate since it is live-in
// x is both live-in and live-out, and written, cannot be reduction
//
// So, the loop cannot be parallelized
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char* argv[])
{
  int len=100; 

  if (argc>1)
    len = atoi(argv[1]);

  int a[len];
  int i,x=10;

#pragma omp parallel for 
  for (i=0;i<len;i++)
  {
    a[i] = x;
    x=i;
  }
  printf("x=%d, a[0]=%d\n",x,a[0]);    
  return 0;
} 

