#include <assert.h>

extern int x;

int f() {
  assert(x == 9);
  return x;
}

int x = 9;

int main() {
  return f();
}
