#include <assert.h>
#include <omp.h>
#include <stdio.h>

int main () {
  int n = 5;
  int arr[5] = {5,3,9,1,7};
  // Reduction combiners
  int max = -10;
  int min = 10;
  int sum = 0;
  int sub = 30;
  int prod = 1;
  _Bool land = 1; /* TRUE */
  int band = ~(arr[0] & 0);
  _Bool lor = 0; /* FALSE */
  int bor = (arr[0] & 0);
  int bxor = (arr[0] & 0);

#pragma omp parallel for reduction(max:max) 
  for (int i=0; i<n; i++)
    max = max < arr[i] ? arr[i] : max;
  assert(max == 9);

#pragma omp parallel for reduction(min:min)
  for (int i=0; i<n; i++)
    min = min > arr[i] ? arr[i] : min;
  assert(min == 1);
  
#pragma omp parallel for reduction(+:sum)
  for (int i=0; i<n; i++)
    sum = sum + arr[i];
  assert(sum == 25);
  
#pragma omp parallel for reduction(-:sub)
  for (int i=0; i<n; i++)
    sub = sub - arr[i];
  assert(sub == 5);
  
#pragma omp parallel for reduction(*:prod)
  for (int i=0; i<n; i++)
    prod = prod * arr[i];
  assert(prod == 945);
  
#pragma omp parallel for reduction(&&:land)
  for (int i=0; i<n; i++)
    land = land && arr[i];
  assert(land);
  
#pragma omp parallel for reduction(&:band)
  for (int i=0; i<n; i++)
    band = band & arr[i];
  assert(band == 1);
  
#pragma omp parallel for reduction(||:lor)
  for (int i=0; i<n; i++)
    lor = lor || arr[i];
  assert(lor);
  
#pragma omp parallel for reduction(|:bor)
  for (int i=0; i<n; i++)
    bor = bor | arr[i];
  assert(bor == 15);
  
#pragma omp parallel for reduction(^:bxor)
  for (int i=0; i<n; i++)
    bxor = bxor ^ arr[i];
  assert(bxor == 9);
}
