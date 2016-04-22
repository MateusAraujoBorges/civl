#include<assert.h>

int main() {
  int i,j,k;

  k = 0;
  for (i = 0, j = 0; i < 10; i++, j++) {
    k += (i + j);
    continue;
  }
  assert(k == 90);

  for (i = 0, j = 0, k = 0; i < 10; i++, j++) {
    if ( k >= 45) continue;
    else
      k += (i + j);
  }
  assert(k == 56);


  for (i = 0, j = 0, k = 0; i < 10; i++, j++) {
    while (1) {
      k += 1;
      if (k <= 45 )
	continue;
      else
	break;
    }
    continue;
  }
  assert(k == 55); 

  for (i = 0, j = 0, k = 0; i < 10; i++, j++) {
    int x = 0;
    
    for (; k < 10; k++, x++)
      continue;
    k+= (i + j);
    if (k > 1000) continue;
  }
  assert(k == 100);
  return 0;
}
