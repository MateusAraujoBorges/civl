#include <assert.h>

int f() {
  int x = 0; // no linkage

  if (1 > 0) {
    extern int x;

    assert(x == 9);
  }
  return x;
}

int x = 9;

int main() {
  return f();
}
