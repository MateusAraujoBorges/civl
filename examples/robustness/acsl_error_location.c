int main () {
  int n = 10;
  int sum = 0;
  
  /*@loop invariant 0 <= i && i <= n;
   *@loop invariant sum = 0;
   *@loop assigns sum;
   *@loop loop variant n-i;
   */
  for (int i=0; i<n; i++)
    sum = sum + i;
  assert(sum == (n-1)*n/2);
}
