// one dimension array computation
int i, a[100];
int main()
{
#pragma omp parallel for
  for (i=0;i<100;i++)
    a[i]=a[i]+1;
  return 0;
} 
