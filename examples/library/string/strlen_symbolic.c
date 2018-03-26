#include <civlc.cvh>
#include <string.h>

$input int LENGTH;
$assume(0 < LENGTH);
$input char STR_IN[LENGTH];

void main(){
  int len = strlen(STR_IN);
  
  $assert(0 <= len && len <= LENGTH);
}
