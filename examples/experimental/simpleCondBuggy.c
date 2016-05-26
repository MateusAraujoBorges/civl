#include<mpi.h>
#include<assert.h>
#include<civlc.cvh>
#include<stdio.h>

$input int x, y;
$input int _mpi_nprocs=2;
//$assume (x > y);

int main() {
  int rank, buf;
  int data[2];

  MPI_Init(NULL, NULL);  
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  if(!rank) 
    data[0] = x;
  else
    data[0] = y;
  data[1] = rank;
  MPI_Allreduce(data, data, 1, MPI_2INT, MPI_MINLOC, MPI_COMM_WORLD);
  printf("data[1] = %d\n", data[1]);
  MPI_Bcast(&buf, 1, MPI_INT, data[1], MPI_COMM_WORLD);
  MPI_Finalize();
  return 0;
}
