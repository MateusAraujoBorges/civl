#include <assert.h>

int x = 9;

int f() {
  assert(x == 9);
  return x;
}

int x;

int main() {
  extern int x;
  return f();
}
