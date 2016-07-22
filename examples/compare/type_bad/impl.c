/* Bad test for comparing functional equivalence which have self-define type.
 */

#ifdef _CIVL
#include <civlc.cvh>
#endif

#include<stdio.h>

typedef int PetscInt;

#ifdef _CIVL
$output PetscInt ARRAY[20];
#endif

int main() {
  int a[5]={1,2,3,4,5};
  
#ifdef _CIVL
  for(int i=0; i<5; i++) {
    ARRAY[i] = a[i];
  }
#endif
}


