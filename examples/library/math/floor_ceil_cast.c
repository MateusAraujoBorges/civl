#include <math.h>
#include <assert.h>

int main() {

  double pi = 3.14;
  double npi = -3.14;

  double f = floor(pi);
  double c = ceil(npi);

  assert(f == (int)pi);
  assert(c == (int)npi);
  return 0;
}
