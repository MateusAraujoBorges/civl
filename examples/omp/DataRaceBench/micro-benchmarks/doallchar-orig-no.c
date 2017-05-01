// one dimension array computation
// with finer granularity than traditional 4 bytes.
// Dynamic tools looking at 4-bytes elements may wrongfuly report race condition.
//
// Liao 2/7/2017
int i; 
char a[100];
int main()
{
#pragma omp parallel for
  for (i=0;i<100;i++)
    a[i]=a[i]+1;
  return 0;
} 
