/* Bad test for comparing functional equivalence which have self-define type.
 */

#ifdef _CIVL
#include <civlc.cvh>
#endif

#include<stdio.h>

typedef int PetscInt;

struct Books {
   int   book_id;
};

#ifdef _CIVL
$output PetscInt ARRAY[5];
$output struct Books booko;
#endif

int main() {
  int b[5];

  for(int i=0;i<5;i++) {
    b[i] = i+1;
  }
#ifdef _CIVL
  booko.book_id = 0;
  for(int i=0; i<5; i++) {
    ARRAY[i] = b[i];
  } 
#endif
}


