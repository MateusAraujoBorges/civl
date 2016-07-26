#include<mpi.h>
#include<assert.h>

/*@
  @ \mpi_collective(MPI_COMM_WORLD, P2P):
  @   requires \mpi_comm_rank == x;
  @*/
void exchange(int x) {
  int y, nprocs;
  int right, left;

  MPI_Comm_size(MPI_COMM_WORLD, &nprocs);
  right = (x + 1) % nprocs;
  left = (x - 1) % nprocs;
  MPI_Sendrecv(&x, 1, MPI_INT, right, 0, &y, 
	       1, MPI_INT, right, 0, 
	       MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  assert(y == left);
}

