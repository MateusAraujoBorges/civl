/* trickydl.c : A tricky deadlocking MPI program.
 * Author: Stephen F. Siegel
 * Date: 2016 Jul 18
 */
#include <mpi.h>
#include <assert.h>

int nprocs, rank, tag=0;
MPI_Comm comm = MPI_COMM_WORLD;
MPI_Status *stat = MPI_STATUS_IGNORE;
int ignore;
int *null = &ignore;

/* Detects buffering.
 * If all communication is synchronous, rank 0 must return 0.
 * If communication can buffer, rank 0 could return 0 or 1.
 * In any case: this function is deadlock-free.
 */
int f() {
  int buf;

  if (rank == 0) {
    MPI_Recv(&buf, 1, MPI_INT, MPI_ANY_SOURCE, tag, comm, stat);
    MPI_Recv(&buf, 1, MPI_INT, MPI_ANY_SOURCE, tag, comm, stat);
    return buf;
  } else if (rank == 1) {
    MPI_Recv(null, 0, MPI_INT, 2, tag, comm, stat);
    buf = 0;
    MPI_Send(&buf, 1, MPI_INT, 0, tag, comm);
  } else if (rank == 2) {
    buf = 1;
    MPI_Send(&buf, 1, MPI_INT, 0, tag, comm);
    MPI_Send(null, 0, MPI_INT, 1, tag, comm);
  }
  return 0;
}

/* Deadlocks iff all communication is synchronous.
 * As long as one 0-byte message can be buffered,
 * no deadlock is possible. */
void g() {
  if (rank == 0) {
    MPI_Send(null, 0, MPI_INT, 1, tag, comm);
    MPI_Recv(null, 0, MPI_INT, 1, tag, comm, stat);
  } else if (rank == 1) {
    MPI_Send(null, 0, MPI_INT, 0, tag, comm);
    MPI_Recv(null, 0, MPI_INT, 0, tag, comm, stat);
  }
}

int main() {
  MPI_Init(NULL, NULL);
  MPI_Comm_size(comm, &nprocs);
  MPI_Comm_rank(comm, &rank);
  assert(nprocs >= 3);
  
  int x = f();

  MPI_Barrier(comm);
  MPI_Bcast(&x, 1, MPI_INT, 0, comm);
  if (x) { g(); }
  MPI_Finalize();
}
