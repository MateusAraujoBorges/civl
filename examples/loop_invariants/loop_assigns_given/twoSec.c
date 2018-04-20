#define M 10
#define N 20
int a[N];

int main() {
  int b[N];

  /*@ loop invariant 0 <= i && i <= N;
    @ loop invariant i <= M ==> (\forall int i1; 0 <= i1 && i1 < i ==> b[i] == 0);
    @ loop invariant i > M ==> (\forall int i1; 0 <= i1 && i1 < M ==> b[i] == 0);
    @ loop invariant \forall int i1; M < i1 && i1 < i ==> b[i] == a[i];
    @ loop assigns i, b[0 .. M-1], b[M .. N-1];
    @*/
  for (int i = 0; i < N; i++) {
    if (i < M) b[i] = 0;
    else if (i > M) b[i] = a[i];
  }
}
