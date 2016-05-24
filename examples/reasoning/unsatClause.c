#include <civlc.cvh>

$input double A,B,C,E,F,G,H,I;

$assume (0 == H*A - G*B);
$assume (0 != I*A - G*C);
$assume (0 != E && 0 != G && 0 != A);
$assume (0 == E*I*A - E*G*C - F*H*A + F*G*B || A == 0);

int main() {
  $assert(0, "unreachable");
}
