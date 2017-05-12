#include<mpi.h>
#include"data_depend_bad.h"

int main(int argc, char** argvs){
  int rank;
  int data = 0;
  
  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  if (rank==0) {
    x = 1;
    MPI_Send(&x, 1, MPI_INT, 1, 0, MPI_COMM_WORLD);
  }
  if (rank==1) {
    MPI_Recv(&x, 1, MPI_INT, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    if (x == 1) 
      MPI_Recv(&x, 1, MPI_INT, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  }
  MPI_Finalize();
}
