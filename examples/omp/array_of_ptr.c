// minimal example to reveal bug in OpenMP Transformer
// when shared variable is an array of pointer.
#include<stdlib.h>

int main() {
  double *a[10]; // array of pointer to double
  
  #pragma omp parallel
  {
    int i;
    #pragma omp for
    for (i=1; i<10; i++) {
      a[i][1] = 2*a[i-1][2];
    }
  }
}
