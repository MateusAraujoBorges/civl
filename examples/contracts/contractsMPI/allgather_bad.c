// How to get rid of BOUNDS ?
/************************** source code  **************************/
#include<mpi.h>
#include<civl-mpi.cvh>
#include<civlc.cvh>
#include<string.h>

#define DATA_LIMIT 1024
#pragma PARSE_ACSL
/*@ 
  @ \mpi_collective(comm, P2P):
  @   requires 0 <= root && root < \mpi_comm_size;
  @   requires \mpi_agree(root) && \mpi_agree(count * \mpi_extent(datatype));
  @   requires 0 <= count && count * \mpi_extent(datatype) < DATA_LIMIT;
  @   requires \mpi_valid(buf, count, datatype);
  @   ensures \mpi_agree(\mpi_region(buf, count, datatype)); 
  @   behavior nonroot:
  @     assumes \mpi_comm_rank != root;
  @     assigns \mpi_region(buf, count, datatype);
  @   waitsfor root;
  @*/
int broadcast(void * buf, int count, 
	      MPI_Datatype datatype, int root, MPI_Comm comm) {
  int nprocs, rank;
  int tag = 999;

  MPI_Comm_size(comm, &nprocs);
  MPI_Comm_rank(comm, &rank);
  if (rank == root) {
    for (int i = 0; i < nprocs; i++)
      if (i != root)
	MPI_Send(buf, count, datatype, i, tag, comm);
  } else
    MPI_Recv(buf, count, datatype, root, tag, comm,
	     MPI_STATUS_IGNORE);
  return 0;
}

/*@ 
  @ \mpi_collective(comm, P2P) :
  @   requires \mpi_agree(root) && \mpi_agree(sendcount * \mpi_extent(sendtype));
  @   requires sendcount * \mpi_extent(sendtype) >= 0 && sendcount * \mpi_extent(sendtype) < DATA_LIMIT;
  @   requires recvcount * \mpi_extent(recvtype) >= 0 && recvcount * \mpi_extent(recvtype) < DATA_LIMIT;
  @   requires 0 <= root && root < \mpi_comm_size;
  @   requires \mpi_valid(sendbuf, sendcount, sendtype);
  @   behavior imroot:
  @     assumes  \mpi_comm_rank == root;
  @     assigns  \mpi_region(recvbuf, recvcount * \mpi_comm_size, recvtype);
  @     requires \mpi_valid(recvbuf, recvcount * \mpi_comm_size, recvtype);
  @     requires recvcount * \mpi_extent(recvtype) == 
  @              sendcount * \mpi_extent(sendtype);
  @     ensures  \mpi_equals(\mpi_region(\mpi_offset(recvbuf, root * sendcount, sendtype), 
  @                                       recvcount, recvtype),
  @                          \mpi_region(sendbuf, sendcount, sendtype)
  @                          );
  @
  @     waitsfor (0 .. \mpi_comm_size-1);
  @   behavior imnroot:
  @     assumes \mpi_comm_rank != root;
  @     ensures \mpi_equals(\mpi_region(sendbuf, sendcount, sendtype),
  @                         \mpi_region(\mpi_offset(\on(root, recvbuf), 
  @                                                 \mpi_comm_rank * sendcount, sendtype),
  @                                     sendcount, sendtype)
  @                        );
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

/*@ \mpi_collective(comm, P2P):
  @   requires \mpi_agree(sendcount * \mpi_extent(sendtype));
  @   requires sendcount >= 0 && sendcount * \mpi_extent(sendtype) * \mpi_comm_size < DATA_LIMIT;
  @   requires recvcount >= 0 && recvcount * \mpi_extent(recvtype) * \mpi_comm_size < DATA_LIMIT;
  @   requires \mpi_valid(sendbuf, sendcount, sendtype);
  @   requires \mpi_valid(recvbuf, recvcount * \mpi_comm_size, recvtype);
  @   requires \mpi_extent(recvtype) * recvcount == \mpi_extent(sendtype) * sendcount;
  @   assigns \mpi_region(recvbuf, recvcount * \mpi_comm_size, recvtype);
  @   ensures \mpi_agree(\mpi_region(recvbuf, recvcount * \mpi_comm_size, recvtype));
  @   ensures \mpi_equals(\mpi_region(sendbuf, sendcount, sendtype),
  @                       \mpi_region(
  @                                   \mpi_offset(recvbuf, \mpi_comm_rank * recvcount + 1, recvtype),
  @                                    recvcount, recvtype));
  @
 */
int allgather(void *sendbuf, int sendcount, MPI_Datatype sendtype,
	      void *recvbuf, int recvcount, MPI_Datatype recvtype,
	      MPI_Comm comm){
  int place;
  int nprocs;

  MPI_Comm_rank(comm, &place);
  MPI_Comm_size(comm, &nprocs);
  gather(sendbuf, sendcount, sendtype,
	 recvbuf, recvcount, recvtype,
	 0, comm);
  broadcast(recvbuf, recvcount*nprocs, recvtype, 0, comm);
  return 0;
}
