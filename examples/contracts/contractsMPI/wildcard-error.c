#include <mpi.h>

int size, rank, x;
int root;

/*@ \mpi_collective[p2p, MPI_COMM_WORLD]:
  @   requires rank == \mpi_comm_rank;
  @   requires size == \mpi_comm_size;
  @   requires 0 <= root < \mpi_comm_size;
  @   ensures \remote(x, root) == size - 1 || 
  @           (\remote(x, root) == size - 2 && rank == root);     // The ensurance will not hold due to the wildcard.
  @*/
void wildcard() {
  if (rank == root) 
    for (int i = 0; i < size; i++)
      if (i != root)
	MPI_Recv(&x, 1, MPI_INT, MPI_ANY_SOURCE, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  else
    MPI_Send(&rank, 1, MPI_INT, 0, 0, MPI_COMM_WORLD);
}
