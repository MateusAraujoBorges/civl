#include <mpi.h>
#include <stdlib.h>
#include <assert.h>

int main(int argc, char * argv[]) {
  int deno = 0;
  int * p = (int *)malloc(sizeof(int) * 3);
  
  MPI_Init(&argc, &argv);
  free(p);
  *p = 0;
  assert(p);
  MPI_Finalize();
  return 0;
}
