#include <mpi.h>
#include <stdio.h>

int main(int argc, char * argv[]) {
  float deno = 0.0;
  float undef;
  
  MPI_Init(&argc, &argv);
  undef = 4 / deno;
  MPI_Finalize();
  return 0;
}
