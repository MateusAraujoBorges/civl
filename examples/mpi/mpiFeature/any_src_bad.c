/* Example contains wildcard receive. This program requires at least 3
   processes. */
#include <mpi.h>
#include <stdlib.h>
#define comm MPI_COMM_WORLD

int main(int argc, char * argv[]) {
  int rank;
  
  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  if (rank == 0) {
    MPI_Recv(NULL, 0, MPI_INT, MPI_ANY_SOURCE, 0, comm, MPI_STATUS_IGNORE);
    MPI_Recv(NULL, 0, MPI_INT, 2, 0, comm, MPI_STATUS_IGNORE);
  }
  else if (rank == 1)
    MPI_Send(NULL, 0, MPI_INT, 0, 0, comm);
  else if (rank == 2)
    MPI_Send(NULL, 0, MPI_INT, 0, 0, comm);
  MPI_Finalize();
}
