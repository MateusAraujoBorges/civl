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

union Data {
   int i;
};

#ifdef _CIVL
$output PetscInt ARRAY[20];
$output struct Books booko;
#endif

int main() {
  struct Books book;
  union Data data;
  int a[5]={1,2,3,4,5};
  
  a[0] += book.book_id;
  a[0] += data.i;
  
#ifdef _CIVL
  booko.book_id = 0;
  for(int i=0; i<5; i++) {
    ARRAY[i] = a[i];
  }
#endif
}


