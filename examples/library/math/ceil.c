#include <math.h>
#include <assert.h>

int main() {
  double pi = 3.14;
  float pif = 3.14f;
  double f = ceil(pi);

  assert(f == 4);

  f = ceilf(pif);
  assert(f == 4);
  return 0;
}
