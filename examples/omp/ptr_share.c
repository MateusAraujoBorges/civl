
int main() {
  int x;
  int *p = &x;
#pragma omp parallel shared(x, p)
  *p=1;
}
