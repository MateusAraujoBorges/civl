#include <mpi.h>

int size, rank, x;
int root;

/*@ \mpi_collective(MPI_COMM_WORLD, P2P):
  @   requires rank == \mpi_comm_rank;
  @   requires size == \mpi_comm_size;
  @   requires 0 <= root < \mpi_comm_size;
  @   ensures \on(root, x) == size - 1 || 
  @           (\on(root, x) == size - 2 && rank == root);     // The ensurance will not hold due to the wildcard.
  @*/
int wildcard() {
  if (rank == root) 
    for (int i = 0; i < size; i++)
      if (i != root)
	MPI_Recv(&x, 1, MPI_INT, i, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  else
    MPI_Send(&rank, 1, MPI_INT, 0, 0, MPI_COMM_WORLD);
}
