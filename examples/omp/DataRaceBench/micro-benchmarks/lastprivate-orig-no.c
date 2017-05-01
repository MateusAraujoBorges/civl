// Using lastprivate() to handle an output dependence.
//
// x: not live-in, yes live-out
//    outer scope
//    loop-carried output-dependence: x=... : accept values based on loop variable; or not. 
//
// Semantics of lastprivate (x)
// causes the corresponding original list item to be updated after the end of the region.
// The compiler/runtime copies the local value back to the shared one within the last iteration.
#include <stdio.h>

void foo()
{
  int i,x;
#pragma omp parallel for private (i) lastprivate (x)
  for (i=0;i<100;i++)
    x=i;
  printf("x=%d",x);
}

int main()
{
  foo();
  return 0;
}

