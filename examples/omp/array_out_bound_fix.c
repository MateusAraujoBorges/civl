//#include <omp.h>

int main(){
  int i = 0;
  int *p = &i;
  int a[2];
  
#pragma omp parallel for
  for(i=1; i<10; i++){
    a[i] = a[*p + i + 1];
  }
}
