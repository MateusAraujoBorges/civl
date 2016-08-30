#include <civlc.cvh>

// x, y are symbolic 
$input int x;
$input int y;

int main() {
  int z = 0;
  if (x>0) {
    z = z + x;
  }
  if (y>0) {
    z = z + y;
  }
  if (y==x) {
    z = z - 2*x;
  }
  $assert(z == 0);
}
