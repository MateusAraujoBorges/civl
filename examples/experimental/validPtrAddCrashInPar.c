#include <assert.h>
#include <mpi.h>

int main(int argc, char * argv[]) {
  int deno = 0;
  int undef;
  int a[3];
  int * p = a;

  MPI_Init(NULL, NULL);  
  p = p + 3;
  assert(p);
  MPI_Finalize();
  return 0;
}
