#include<stdio.h>
#include<stdlib.h>
#include <civlc.cvh>

#pragma CIVL ACSL

$input int N;
$assume(N >= 0);
$input int a[N];
$output double __sum;


int main(int argc, char *argv[]) {
  double sum = 0;
  int i, n = N;
  
  /*@ loop invariant 0 <= i <= n;
    @ loop invariant sum == \sum(0, i-1, \lambda int t; a[t]);
    @ loop assigns sum, i;
    @*/
  for (i=0; i<n; i++) sum += a[i];
  __sum = sum;
  printf("result is %lf\n", sum);
  return 0;
}
