#include<mpi.h>
#include"data_depend_bad.h"

int main(int argc, char** argvs){
  int rank;
  int data[2];
  
  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  if (rank==0) {
    data[0] = 1;
    data[1] = 2;
    MPI_Send(data, 2, MPI_INT, 1, 0, MPI_COMM_WORLD);
  }
  if (rank==1) {
    MPI_Recv(data, 2, MPI_INT, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    if (data[0] != 1 || data[1] != 2) 
      MPI_Recv(data, 2, MPI_INT, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  }
  MPI_Finalize();
}
