#include <mpi.h>
#include <stdio.h>
#include <assert.h>


int main() {
  int rank;
  double prefixSums[3];
  double values[3] = {1, 2, 3};

  MPI_Init(NULL, NULL);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);

  MPI_Exscan(values, prefixSums, 3, MPI_DOUBLE, MPI_SUM, MPI_COMM_WORLD);
  
  printf("I'm rank %d, my results are %f, %f, %f\n", rank, prefixSums[0], prefixSums[1], prefixSums[2]);
  if (rank > 0)
  assert(prefixSums[0] == rank && prefixSums[1] == 2 * (rank)
	 && prefixSums[2] == 3 * (rank));
  MPI_Finalize();
  return 0;
}
