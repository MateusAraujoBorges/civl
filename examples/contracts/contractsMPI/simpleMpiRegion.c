#include<mpi.h>
#include<assert.h>


#define comm MPI_COMM_WORLD

/*@ \mpi_collective(comm, P2P):
  @   ensures \mpi_agree(\mpi_region(x, 2, MPI_DOUBLE));
  @*/
int bcast(void * x) {
  return 0;
}


/*@
  @ \mpi_collective(comm, P2P):
  @   ensures \mpi_agree(\result);
  @*/
double target() {
  double data[2];

  bcast(data);
  return data[1];
}
