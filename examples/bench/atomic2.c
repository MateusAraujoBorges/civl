#include<stdbool.h>
#include<assert.h>
#include<civlc.cvh>
$input int x;
_Bool b=true;

void foo(){
  $atomic{
    b=false;
    $when(x>0);
    b=true;
  }
}

void main(){
  $proc p=$spawn foo();
  assert(b);
  $wait(p);
}
