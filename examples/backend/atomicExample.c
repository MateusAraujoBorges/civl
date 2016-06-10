#include<stdbool.h>
#include<assert.h>
#include<civlc.cvh>
$input int x;
_Bool b=true;
int a=0;

void foo(){
  $atomic{
    b=false;
    $when(x>0);
    b=true;
  }
}

void goo(){
  if(!b)
    a=1;
}

void main(){
  $proc pf, pg;

  $atomic{
    pf=$spawn foo();
    pg=$spawn goo();
  }
  $wait(pg);
  assert(a==0);
  assert(b);
  $wait(pf);
}
