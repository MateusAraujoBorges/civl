//#include<mpi.h>
#include<civlc.cvh>
#include<stdio.h>

/*@ 
  @ ensures \result == 2*x; 
  @*/
$atomic_f int g(int x){
  return 2*x;
}

/*@
  @ requires x==0 && y>x && y<=4;
  @ ensures \result==\sum(x,y, \lambda int i; 2*i);
  @*/
int f(int x, int y){
  int r=0;

  for(int i=x; i<=y; i++)
    r+=i*2;
  printf("x=%d, y=%d, result=%d\n", x, y, r);
  return r;
}
