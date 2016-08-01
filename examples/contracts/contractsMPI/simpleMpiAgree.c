#include<mpi.h>
#include<assert.h>


#define comm MPI_COMM_WORLD

/*@ requires \valid(x);
  @ \mpi_collective(comm, P2P):
  @    ensures \mpi_agree(*x);
  @*/
int bcast(int * x) {
  return 0;
}


/*@
  @ \mpi_collective(comm, P2P):
  @   ensures \mpi_agree(\result);
  @*/
int target() {
  int rank;

  $havoc(&rank);
  bcast(&rank);
  return rank;
}
