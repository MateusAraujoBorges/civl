#include <mpi.h>
#include <civl-mpi.cvh>


#define

int main() {
  MPI_Init(NULL, NULL);

  MPI_Datatype datatype;  
  void * buf = NULL;
  double * dbuf;

  $havoc(&datatype);
  $assume(datatype == MPI_DOUBLE || datatype == MPI_INT || datatype == MPI_CHAR || datatype == MPI_2INT);
  buf = $mpi_valid(2, datatype);
  if (datatype == MPI_DOUBLE) {
    dbuf = (double *)buf;
    dbuf[0] = 2.0;
    $assert(dbuf[0] > 0);
  }
  $free(buf);
  MPI_Finalize();
}
