#include <civlc.cvh>
#include <string.h>

$input int LENGTH;
$assume(0 < LENGTH);
$input char STR_IN[2][LENGTH];

void main(){
  int len = strlen(&STR_IN[1][1]);
  
  $assert(0 <= len);
}
