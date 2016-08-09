#include<mpi.h>
#include<assert.h>


#define comm MPI_COMM_WORLD


/*@ \mpi_collective(comm, P2P):
  @   ensures \mpi_agree(\mpi_region(x, 2, MPI_DOUBLE));
  @*/
int bcast(void * x, MPI_Datatype datatype) {
  return 0;
}


/*@
  @ \mpi_collective(comm, P2P):
  @   requires \mpi_valid(data, 2, MPI_DOUBLE) && \mpi_agree(datatype);
  @ 
  @*/
double target(void * data, MPI_Datatype datatype) {
  bcast(data, datatype);
  return 0;
}
