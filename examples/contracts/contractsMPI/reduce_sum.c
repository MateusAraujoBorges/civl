#include<mpi.h>
#include<civl-mpi.cvh>
#include<civlc.cvh>
#include<string.h>
#include<stdlib.h>

/* A collective sum-reduction operation */

/*@ \mpi_collective(comm, P2P):
  @   requires count > 0;
  @   requires \mpi_valid(sendbuf, datatype, count);
  @   requires \mpi_valid(recvbuf, datatype, count);
  @   requires \mpi_agree(root) && \mpi_agree(count);
  @   requires 0 <= root && root < \mpi_comm_size;
  @   ensures  \forall integer i; 0<= i <count ==> 
  @                recvbuf[i] == \sum(0, \mpi_comm_size, 
  @                \lambda int k; \on(sendbuf[i], k));
  @   waitsfor root;
  @
  @*/
int reduce_sum(const void* sendbuf, void* recvbuf, MPI_Datatye datatype,
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
