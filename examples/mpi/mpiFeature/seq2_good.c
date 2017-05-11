#include <mpi.h>
#include <stdio.h>

int main(int argc, char * argv[]) {
  int undef = 1;
  int a[3];
  int * p = a;
  
  MPI_Init(&argc, &argv);
  *p = undef;
  MPI_Finalize();
  return 0;
}
