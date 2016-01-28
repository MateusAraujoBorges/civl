#include <civlc.cvh>
#include <stdio.h>

$input int A_BOUND;
$input int B_BOUND;
$input int A;
$input int B;
$assume (A>0 && B>0 && A<A_BOUND && B<B_BOUND);
/*
command: civl verify -inputA_BOUND=4 -inputB_BOUND=6 problem1.c
*/
int myGCD(int a, int b){
  while(a != b){
    if(a > b)
      a = a-b;
    if(b > a)
      b = b-a;
  }
  return a;
}

void main(){
  int result1 = myGCD(A, B);
  int minAB = A < B ? A : B;
  $assert($forall {i = (result1+1) .. (minAB)} (A%i != 0 || B%i != 0));
  $assert( A%result1 == 0 && B%result1 == 0);
}
