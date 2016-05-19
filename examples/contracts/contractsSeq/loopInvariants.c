#include <assert.h>
#include <civlc.cvh>

$input int n;
$input int m;
$assume(n > m && m > 0);
int main() {
  int i = 0;
  int x = 0;

  /*@ loop invariant x * 2 == i * (i + 1);
  */
  while (i < n)
    x += (i++);
  assert(2 * x == n * (n - 1));
  return 0;
}
