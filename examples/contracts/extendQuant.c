//#include<mpi.h>
#include<civlc.cvh>

/*@ 
  @ ensures \result == 2*x; 
  @*/
$atomic_f int g(int x){
  return 2*x;
}

/*@
  @ requires x==0 && y==3;
  @ ensures \result==\sum(x,y, \lambda int i; 2*i);
  @*/
int f(int x, int y){
  int r=0;

  for(int i=x; i<=y; i++)
    r+=i*2;
  return r;
}
