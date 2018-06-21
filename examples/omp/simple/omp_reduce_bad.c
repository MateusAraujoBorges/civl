#include <assert.h>
#include <omp.h>
#include <stdio.h>

int main () {
  int n = 5;
  int arr[5] = {5,3,9,1,7};
  // Reduction combiners
  int res = 0;

#pragma omp parallel for reduction(undecl_id:res) 
  for (int i=0; i<n; i++)
    max = max < arr[i] ? arr[i] : max;
  assert(max == 9);
}
