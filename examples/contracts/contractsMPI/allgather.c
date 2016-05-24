#include<mpi.h>
#include<civl-mpi.cvh>
#include<civlc.cvh>
#include<string.h>

/*@ 
  @ requires \valid(buf + (0 .. count));
  @ \mpi_collective(comm, P2P):
  @   requires 0 <= root && root < \mpi_comm_size;
  @   requires \mpi_agree(root) && \mpi_agree(count);
  @   requires 0 < count && count <= 3;
  @   ensures \mpi_equals(buf, count, MPI_INT, \remote(buf, root));
  @   waitsfor root;
  @*/
int broadcast(int * buf, int count, 
	      MPI_Datatype datatype, int root, MPI_Comm comm) {
  int nprocs, rank;
  int tag = 999;

  MPI_Comm_size(comm, &nprocs);
  MPI_Comm_rank(comm, &rank);
  if (rank == root) {
    for (int i = 0; i < nprocs; i++)
      if (i != root)
	MPI_Send(buf, count, MPI_INT, i, tag, comm);
  } else
    MPI_Recv(buf, count, MPI_INT, root, tag, comm,
	     MPI_STATUS_IGNORE);
  return 0;
}


/*@ 
  @ \mpi_collective(comm, P2P) :
  @   requires \mpi_agree(root) && \mpi_agree(sendcount);
  @   requires sendcount > 0 && sendcount < 3;
  @   requires recvcount > 0 && recvcount < 3;
  @   requires 0 <= root && root < \mpi_comm_size;
  @   requires \valid(sendbuf + (0 .. sendcount));
  @   behavior imroot:
  @     assumes  \mpi_comm_rank == root;
  @     requires \valid(recvbuf + (0 .. recvcount * \mpi_comm_size));
  @     requires recvcount == sendcount;
  @     ensures  \mpi_equals((recvbuf + root * sendcount), sendcount, MPI_INT, sendbuf);
  @     ensures  \forall int i; i >= 0 && i < \mpi_comm_size ==>
  @              \mpi_equals((recvbuf + i * sendcount), sendcount, MPI_INT, \remote(sendbuf, i));
  @     waitsfor (0 .. \mpi_comm_size-1);
  @   behavior imnroot:
  @     assumes  \mpi_comm_rank != root;
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
    
    ptr = $mpi_pointer_add(recvbuf, root * recvcount, MPI_INT);
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
	ptr = $mpi_pointer_add(recvbuf, offset, MPI_INT);
	MPI_Recv(ptr, recvcount, MPI_INT, i, tag, comm,
		 &status);
      }
    }
  }
  return 0;
}

/*@ \mpi_collective(comm, P2P):
  @   requires \mpi_agree(sendcount);
  @   requires sendcount > 0 && sendcount < 2;
  @   requires recvcount > 0 && recvcount < 2;
  @   requires \valid(sendbuf + (0 .. sendcount));
  @   requires \valid(recvbuf + (0 .. (recvcount * \mpi_comm_size)));
  @   requires recvcount == sendcount;
  @   ensures  \forall int i; 0<=i && i<\mpi_comm_size ==>
  @                    \mpi_equals((recvbuf + i * recvcount), recvcount, 
  @                     MPI_INT, \remote(sendbuf, i));     
  @   waitsfor 0;
  @
 */
int allgather(int *sendbuf, int sendcount, MPI_Datatype sendtype,
	      int *recvbuf, int recvcount, MPI_Datatype recvtype,
	      MPI_Comm comm){
  int place;
  int nprocs;

  $elaborate(recvcount);
  $elaborate(sendcount);
  MPI_Comm_rank(comm, &place);
  MPI_Comm_size(comm, &nprocs);
  gather(sendbuf, sendcount, sendtype,
	 recvbuf, recvcount, recvtype,
	 0, comm);
  broadcast(recvbuf, recvcount*nprocs, recvtype, 0, comm);
  return 0;
}


int main() {
  broadcast(NULL, 0, MPI_INT, 0, (MPI_Comm)0);
  gather(NULL, 0, MPI_INT, NULL, 0, MPI_INT, 0, (MPI_Comm)0);
  return 0;
}
