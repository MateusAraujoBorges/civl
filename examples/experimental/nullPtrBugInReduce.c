/* Minimal example of a mismatch in collective calls.
 * One proc tries to broadcast then reduce, the others
 * reduce then broadcast.  Call with nprocs=2 or higher.
 */
#include <mpi.h>
#include <stdlib.h>
#define comm MPI_COMM_WORLD

int main(int argc, char * argv[]) {
  int rank;
  int x = 1;

  MPI_Init(&argc, &argv);
  MPI_Comm_rank(comm, &rank);
  if (rank == 0) {
    MPI_Bcast(NULL, 0, MPI_INT, 0, comm);
    MPI_Reduce(NULL, NULL, 0, MPI_INT, MPI_SUM, 0, comm);
  } else {
    MPI_Bcast(NULL, 0, MPI_INT, 0, comm);
    MPI_Reduce(NULL, NULL, 0, MPI_INT, MPI_SUM, 0, comm);
  }
  MPI_Finalize();
}
