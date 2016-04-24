#include<stdio.h>
int f(int n, int a[][n]) {
  int s=0;
  
  for(int i=0; i<n; i++){
    s+=a[0][i];
  }
  return s;
}

int main() {
  int b[10][10];

  for(int i=0; i<10; i++){
    for(int j=0; j<10; j++)
      b[i][j]=1;
  }
  int t= f(10, b);
  printf("%d\n", t);
}
