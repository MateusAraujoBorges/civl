#include <civlc.cvh>

$input int offset;
$assume(0<=offset && offset<=1);
int main() {
  int a = 8;
  void *p = &a + 1;
  void *q = p + offset;

  return 0;
}
