#include <civlc.cvh>
$input int N, M;
$assume(N >= 0);
$assume(M >= 0);
int main() {
  int n;
  int a[N][M];

  a[0][0] = 0;

  $havoc(&n);

  int b[n];

  b[0] = 0;
}

