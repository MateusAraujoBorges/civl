#include <mpi.h>

int size, rank;
int root;
int x;

/*@ \mpi_collective(MPI_COMM_WORLD, P2P):
  @   requires rank == \mpi_comm_rank;
  @   requires size == \mpi_comm_size;
  @   requires 0 <= root && root < \mpi_comm_size;
  @   requires \mpi_agree(root);
  @   requires datatype == MPI_INT;
  @   ensures \on(root, x) == size - 1 || 
  @           (\on(root, x) == size - 2 && size - 1 == root); 
  @*/
int wildcard(MPI_Datatype datatype) {
  if (rank == root) {
    for (int i = 0; i < size; i++)
      if (i != root)
	MPI_Recv(&x, 1, datatype, i, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  } else
    MPI_Send(&rank, 1, datatype, root, 0, MPI_COMM_WORLD);
  return 0;
}
