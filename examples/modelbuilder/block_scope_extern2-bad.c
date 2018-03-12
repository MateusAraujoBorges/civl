#include <assert.h>

int f() {
  int x = 0; // no linkage

  if (1 > 0) {
    assert(x == 0); // the x of no linkage
 
    extern int x;

    assert(x == 9); // the x of external-linkage
    x = 3;          
    assert(x == 3); 
  }
  return x;
}

int x = 9;

int main() {
  x = f();
  assert(x == 3); // the x of external-linkage
}
