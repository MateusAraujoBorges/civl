#include<mpi.h>
#include<civlc.cvh>
#include<string.h>
#include<stdlib.h>

/* A collective sum-reduction operation */

int reduce_sum(void* sendbuf, void* recvbuf, MPI_Datatype datatype,
	       int count, int root, MPI_Comm comm) {
  int rank;
  int REDUCE_TAG = 999;

  MPI_Comm_rank(comm, &rank);
  if (rank != root)
    MPI_Send(sendbuf, count, datatype, root, REDUCE_TAG, comm);
  else {
    int nprocs;
    int size;
    int * sum;

    MPI_Comm_size(comm, &nprocs);
    size = count * sizeof(int);
    memcpy(recvbuf, sendbuf, size);
    sum = (int *)malloc(sizeof(int) * count);
    for (int i = 0; i<nprocs; i++) {
      if (i != root){
	MPI_Recv(recvbuf, count, datatype, i, REDUCE_TAG, comm, MPI_STATUS_IGNORE);

	for (int i = 0; i < count; i++) 
	  sum[i] = sum[i] + recvbuf[i];
      }
    }
    memcpy(recvbuf, sum, size);
  }
  return 0;
}
