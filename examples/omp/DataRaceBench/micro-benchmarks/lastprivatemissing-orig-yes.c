// x: not live-in, yes live-out
//    outer scope
//    loop-carried output-dependence: x=... : accept values based on loop variable; or not. 
//Solution: Can be parallelized using lastprivate(x)
//
// Semantics of lastprivate (x)
// causes the corresponding original list item to be updated after the end of the region.
// The compiler/runtime copies the local value back to the shared one within the last iteration.
// Without lastprivate(x), there will be data race for x.
#include <stdio.h>
int main(int argc, char* argv[])
{
  int i,x;
  int len = 10000;

#pragma omp parallel for private (i) 
  for (i=0;i<len;i++)
    x=i;

  printf("x=%d",x);
  return 0;
}

