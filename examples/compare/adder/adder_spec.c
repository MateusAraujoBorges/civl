#include<stdio.h>
#include<stdlib.h>

#ifdef _CIVL
#include <civlc.cvh>
$input int NB;
$output double __sum;
#endif

int main(int argc, char *argv[]) {
  double sum = 0;
  int i, n;
  FILE *fp = fopen("data","r");

  n = atoi(argv[1]);
#ifdef _CIVL
  $assume(0 < n && n <= NB);
#endif

  double a[n];

  for (i=0; i<n; i++) fscanf(fp, "%lf", &a[i]);
  for (i=0; i<n; i++) sum += a[i];
#ifdef _CIVL
  __sum = sum;
#endif
  printf("result is %lf\n", sum);
  fclose(fp);
  return 0;
}
