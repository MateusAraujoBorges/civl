#include<mpi.h>
#include<assert.h>


#define comm MPI_COMM_WORLD

/*@ \mpi_collective(comm, P2P):
  @   ensures \mpi_agree(\mpi_region(\mpi_offset(x, 1, datatype)
  @                                  , 1, datatype));
  @*/
int bcast(void * x, MPI_Datatype datatype) {
  return 0;
}


/*@
  @ \mpi_collective(comm, P2P):
  @   requires \mpi_valid(buf, 2, datatype);
  @   ensures \mpi_agree(\mpi_region(\mpi_offset(buf, 1, datatype)
  @                                  , 1, datatype));
  @*/
int target(void * buf, MPI_Datatype datatype) {
  bcast(buf, datatype);
  return 0;
}
