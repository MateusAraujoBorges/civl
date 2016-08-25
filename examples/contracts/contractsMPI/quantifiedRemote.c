#include <mpi.h>
/*@
  @ \mpi_collective(MPI_COMM_WORLD, P2P):
  @  requires \forall int i; 0<=i && i<n
  @            ==> x[i] == \on(0, x[i]);
  @*/
int foo(int x[], int n) {
  return x[n-1];
}
