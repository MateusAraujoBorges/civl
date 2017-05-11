#include<mpi.h>
#include"data_depend_good.h"

int main(int argc, char** argvs){
  int rank;
  
  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  if (rank==0) {
    int x = 0;

    MPI_Send(&x, 1, MPI_INT, 1, 0, MPI_COMM_WORLD);
  }
  if (rank==1) {
    int x = 1;

    MPI_Recv(&x, 1, MPI_INT, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    if (x == 1)
	MPI_Recv(&x, 1, MPI_INT, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  }
  MPI_Finalize();
}
