#include<mpi.h>
#include<civl-mpi.cvh>
#include<civlc.cvh>
#include<string.h>
#include<stdio.h>

/*@ 
  @ \mpi_collective(comm, P2P) :
  @   requires \mpi_agree(root) && \mpi_agree(sendcount);
  @   requires sendcount > 0 && sendcount < 10;
  @   requires recvcount > 0 && recvcount < 10;
  @   requires 0 <= root && root < \mpi_comm_size;
  @   requires \valid(sendbuf + (0 .. sendcount));
  @   behavior imroot:
  @     assumes  \mpi_comm_rank == root;
  @     requires \valid(recvbuf + (0 .. recvcount * \mpi_comm_size));
  @     requires recvcount == sendcount;
  @     ensures  \mpi_equals((recvbuf + root * sendcount), sendcount, MPI_INT, sendbuf);
  @   behavior imnroot:
  @     assumes  \mpi_comm_rank != root;
  @     requires \mpi_equals(sendbuf, sendcount, MPI_INT, 
  @              (\remote(recvbuf, root) + \mpi_comm_rank * sendcount));
  @*/
int gather(int* sendbuf, int sendcount, MPI_Datatype sendtype, 
	   int* recvbuf, int recvcount, MPI_Datatype recvtype,
	   int root, MPI_Comm comm){
  int rank, nprocs;
  MPI_Status status;
  int tag = 998;

  MPI_Comm_rank(comm, &rank);
  MPI_Comm_size(comm, &nprocs);
  if(root == rank) {
    void *ptr;
    
    ptr = $mpi_pointerAdd(recvbuf, root * recvcount, MPI_INT);
    $elaborate(recvcount);
    memcpy(ptr, sendbuf, recvcount * sizeofDatatype(MPI_INT));
  }else
    MPI_Send(sendbuf, sendcount, MPI_INT, root, tag, comm);
  if(rank == root) {
    int real_recvcount;
    int offset;

    for(int i=0; i<nprocs; i++) {
      if(i != root) {
	void * ptr;

	offset = i * recvcount;
	ptr = $mpi_pointerAdd(recvbuf, offset, MPI_INT);
	MPI_Recv(ptr, recvcount, MPI_INT, i, tag, comm,
		 &status);
      }
    }
  }
  sendbuf[0] = rank;
  return 0;
}


int main() {
  gather(NULL, 0, MPI_INT, NULL, 0, MPI_INT, 0, (MPI_Comm)0);
  return 0;
}
