#include<mpi.h>
#include<civl-mpi.cvh>
#include<civlc.cvh>
#include<string.h>
#include<stdio.h>

/*@ 
  @ \mpi_collective(comm, P2P) :
  @   requires \mpi_agree(root) && \mpi_agree(sendcount * \mpi_extent(sendtype));
  @   requires sendcount > 2 && sendcount * \mpi_extent(sendtype) < 5;
  @   requires recvcount > 2 && recvcount * \mpi_extent(recvtype) < 5;
  @   requires 0 <= root && root < \mpi_comm_size;
  @   requires \mpi_valid(sendbuf, sendcount, sendtype);
  @   behavior imroot:
  @     assumes  \mpi_comm_rank == root;
  @     requires \mpi_valid(recvbuf, recvcount * \mpi_comm_size, recvtype);
  @     requires recvcount * \mpi_extent(recvtype) == 
  @              sendcount * \mpi_extent(sendtype);
  @     ensures  \mpi_equals(\mpi_offset(recvbuf, root * sendcount, sendtype), sendcount, sendtype, sendbuf);
  @   behavior imnroot:
  @     assumes  \mpi_comm_rank != root;
  @     ensures \mpi_equals(sendbuf, sendcount, sendtype, 
  @              \mpi_offset(\on(root, recvbuf), \mpi_comm_rank * sendcount, sendtype));
  @*/
int gather(void* sendbuf, int sendcount, MPI_Datatype sendtype, 
	   void* recvbuf, int recvcount, MPI_Datatype recvtype,
	   int root, MPI_Comm comm){
  int rank, nprocs;
  MPI_Status status;
  int tag = 998;

  MPI_Comm_rank(comm, &rank);
  MPI_Comm_size(comm, &nprocs);
  if(root == rank) {
    void *ptr;
    
    ptr = $mpi_pointer_add(recvbuf, root * recvcount, recvtype);
    memcpy(ptr, sendbuf, recvcount * sizeofDatatype(recvtype));
  }else
    MPI_Send(sendbuf, sendcount, sendtype, root, tag, comm);
  if(rank == root) {
    int real_recvcount;
    int offset;

    for(int i=0; i<nprocs; i++) {
      if(i != root) {
	void * ptr;

	offset = i * recvcount;
	ptr = $mpi_pointer_add(recvbuf, offset, recvtype);
	MPI_Recv(ptr, recvcount, recvtype, i, tag, comm,
		 &status);
      }
    }
  }
  return 0;
}

