#include <math.h>
#include <assert.h>

int main() {
  double pi = 3.14;
  float pif = 3.14f;
  double f = floor(pi);

  assert(f == 3);

  f = floorf(pif);
  assert(f == 3);
  return 0;
}
