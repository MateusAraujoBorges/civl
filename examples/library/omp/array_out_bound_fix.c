//#include <omp.h>

int main(){
  int i = 0;
  int *p = &i;
  int a[12];
  int b[12];
  
#pragma omp parallel for
  for(i=1; i<5; i++){
    b[i] = a[*p + i +1];
  }
}
