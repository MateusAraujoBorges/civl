#include <civlc.cvh>

$input int A;
$input int B;

int main(){
  int a = A/B;
  $assert($forall (int i: 1 .. 3) A/i == 0);
  $assert(A/B == 0);
  $assert($exists (int i: 1 .. 3) $forall (int j: i .. 3) i/j == 0);
}
