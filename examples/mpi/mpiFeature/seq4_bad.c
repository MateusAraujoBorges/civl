#include <mpi.h>
#include <stdio.h>

int main(int argc, char * argv[]) {
  int deno = 0;
  int undef;
  int a[3];
  int * p = a;
  
  MPI_Init(&argc, &argv);
  p = a + 5;
  MPI_Finalize();
  return 0;
}
