#include <assert.h>
#include "file_scope_extern3_lib.h"

extern Type t;

int f() {
  assert(value(t) == 9);
  return 0;
}

int main() {
  return f();
}
