int main() {
  int x = 0;
#pragma omp parallel shared(x)
  {
#pragma omp atomic
    x=x+1;
  }
}
