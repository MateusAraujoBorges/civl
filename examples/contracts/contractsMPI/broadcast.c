#include<mpi.h>
#include<civlc.cvh>
#include<stdio.h>
#pragma CIVL ACSL

#define DATA_LIMIT 1024

/*@ 
  @ \mpi_collective(comm, P2P):
  @   requires 0 <= root && root < \mpi_comm_size;
  @   requires \mpi_agree(root) && \mpi_agree(count * \mpi_extent(datatype));
  @   requires 0 < count && count * \mpi_extent(datatype) < DATA_LIMIT;
  @   requires \mpi_valid(buf, count, datatype);
  @   ensures \mpi_agree(\mpi_region(buf, count, datatype)); 
  @   behavior nonroot:
  @     assumes \mpi_comm_rank != root;
  @     assigns \mpi_region(buf, count, datatype);
  @     waitsfor root;
  @*/
int broadcast(void * buf, int count, 
	      MPI_Datatype datatype, int root, MPI_Comm comm) {
  int nprocs, rank;
  int tag = 999;

  MPI_Comm_size(comm, &nprocs);
  MPI_Comm_rank(comm, &rank);
  printf("my rank:%d, root:%d\n", rank, root);
  if (rank == root) {
    for (int i = 0; i < nprocs; i++)
      if (i != root)
	MPI_Send(buf, count, datatype, i, tag, comm);
  } else
    MPI_Recv(buf, count, datatype, root, tag, comm,
	     MPI_STATUS_IGNORE);
  return 0;
}
