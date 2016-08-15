#include<mpi.h>
#include<civl-mpi.cvh>
#include<civlc.cvh>
#include<string.h>

/*@ \mpi_collective(comm, P2P):
  @   requires \mpi_agree(root) && \mpi_agree(recvcount * \mpi_extent(recvtype));
  @   requires \mpi_valid(recvbuf, recvcount, recvtype);
  @   requires 0 <= root && root < \mpi_comm_size;
  @   requires sendcount >= 0 && sendcount * \mpi_extent(sendtype) < 5;
  @   requires recvcount >= 0 && recvcount * \mpi_extent(recvtype) < 5;
  @   assigns  \mpi_region(recvbuf, recvcount, recvtype);
  @   behavior imroot:
  @     assumes \mpi_comm_rank == root;
  @     requires \mpi_extent(sendtype) * sendcount == 
  @              \mpi_extent(recvtype) * recvcount;
  @     requires \mpi_valid(sendbuf, sendcount * \mpi_comm_size, sendtype);
  @     ensures  \mpi_equals(recvbuf, recvcount, recvtype, 
  @                          \mpi_offset(sendbuf, \mpi_comm_rank * sendcount,
  @                                   sendtype));
  @   behavior noroot:
  @     assumes \mpi_comm_rank != root;
  @     ensures \mpi_equals(recvbuf, recvcount, recvtype,
  @                \mpi_offset(\on(root, sendbuf), 
  @                            recvcount * \mpi_comm_rank, sendtype));
 */
int scatter(const void* sendbuf, int sendcount, MPI_Datatype sendtype, 
		 void* recvbuf, int recvcount, MPI_Datatype recvtype, int root,
		 MPI_Comm comm){
  int rank, nprocs;
  int tag = 999;

  MPI_Comm_rank(comm, &rank);
  MPI_Comm_size(comm, &nprocs);

  if (rank == root) {
    void * ptr;
    int offset;

    ptr = $mpi_pointer_add(sendbuf, root*sendcount, sendtype);
    memcpy(recvbuf, ptr, sizeofDatatype(recvtype)*recvcount);
    for(int i=0; i<nprocs; i++){
      if(i != root) {
	void * ptr;

	offset = i * sendcount;
	ptr = $mpi_pointer_add(sendbuf, offset, sendtype);
	MPI_Send(ptr, sendcount, sendtype, i, tag, comm);
      }
    }
  }else
    MPI_Recv(recvbuf, recvcount, recvtype, 
	     root, tag, comm, MPI_STATUS_IGNORE);
  return 0;
}
