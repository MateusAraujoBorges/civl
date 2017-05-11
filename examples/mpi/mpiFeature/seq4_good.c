#include <mpi.h>
#include <assert.h>

int main(int argc, char * argv[]) {
  int deno = 0;
  int undef;
  int a[3];
  int * p = a;
  
  MPI_Init(&argc, &argv);
  assert(a + 3);
  MPI_Finalize();
  return 0;
}
