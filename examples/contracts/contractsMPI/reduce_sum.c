#include<mpi.h>
#include<civl-mpi.cvh>
#include<civlc.cvh>
#include<string.h>
#include<stdlib.h>

/* A collective sum-reduction operation */

/*@ \mpi_collective(comm, P2P):
  @   requires datatype == MPI_INT;
  @   requires 0<count && count*\mpi_extent(datatype) < 5;
  @   requires \mpi_valid(sendbuf, count, datatype);
  @   requires \mpi_valid(recvbuf, count, datatype);
  @   requires \mpi_agree(root) && \mpi_agree(count * datatype);
  @   requires 0 <= root && root < \mpi_comm_size;
  @   ensures  \forall integer i; 0<= i && i <count ==> 
  @                recvbuf[i] == \sum(0, \mpi_comm_size-1, 
  @                \lambda int k; \on(k, sendbuf)[i]);
  @   waitsfor root;
  @
  @*/
int reduce_sum(int * sendbuf, int * recvbuf, MPI_Datatype datatype,
	       int count, int root, MPI_Comm comm) {
  int rank;

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
    free(sum);
  }
  
  return 0;
}
