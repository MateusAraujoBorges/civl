#include <stdlib.h>

void main(){
  
  int * p = malloc(sizeof(int));
  *p = 10;
  free(p);
}
