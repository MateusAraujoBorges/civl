/* FILE: mpithreads_sendrecv.c
 *
 * DESCRIPTION: 2 MPI Communicators, each of which groups 2 MPI
 * processes, each MPI process has 1 thread. Threads communicate with
 * each other but no inter-communication.
 * 
 * This program is a CIVL benchmark for POR of MPI programs: Threads
 * will communicate through different communicators are independent
 * with each other.
 * 
 * Author: Ziqing Luo
 *
 */
#include "mpi.h" 
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

typedef struct thread_info Thread_Info;

struct thread_info {
  int tid;
  MPI_Comm comm;
};

void * thread(void * arg) {
  Thread_Info * info = (Thread_Info*)arg;
  int rank;
  
  MPI_Comm_rank(info->comm, &rank);
  if (rank == 0) {
    MPI_Send(NULL, 0, MPI_INT, 1, 0, info->comm);
    MPI_Recv(NULL, 0, MPI_INT, MPI_ANY_SOURCE, 
	     0, info->comm, MPI_STATUS_IGNORE);
  } else {
    MPI_Recv(NULL, 0, MPI_INT, MPI_ANY_SOURCE, 
	     0, info->comm, MPI_STATUS_IGNORE);
    MPI_Send(NULL, 0, MPI_INT, 0, 0, info->comm);
  }
}

int main() {
  int size;
  pthread_t threads[2];
  void * status;
  Thread_Info thread_infos[2];
  int provided;

#ifdef _CIVL
  MPI_Init(NULL, NULL);
#else
  MPI_Init_thread(NULL, NULL, MPI_THREAD_MULTIPLE, &provided);
#endif
  assert(provided == MPI_THREAD_MULTIPLE);
  MPI_Comm_size(MPI_COMM_WORLD, &size);
  assert(size == 2);
  MPI_Comm_dup(MPI_COMM_WORLD, &(&thread_infos[1])->comm);

  thread_infos[0].tid = 0;
  thread_infos[0].comm = MPI_COMM_WORLD;
  thread_infos[1].tid = 1;

  pthread_create(&threads[0], NULL, thread, thread_infos);
  pthread_create(&threads[1], NULL, thread, thread_infos + 1); 
  for (int i = 0; i < 2; i++)
    pthread_join(threads[i], &status);
  MPI_Comm_free(&thread_infos[1].comm);
  MPI_Finalize();
  return 0;
}
