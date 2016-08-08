#include <assert.h>
#include <mpi.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define OWNER(index) ((nprocs*(index+1)-1)/numRow)

int numRow, numCol;
long double data[numRow][numCol];  // input matrix
int * idx;
int * loc;
int localRow;   // number of rows owned by the process
int rank, nprocs;
int first;      // the global index of the first row in original 
                // matrix


/* Performs a gaussian elimination on the given matrix, the output
 * matrix will finally be in row echelon form .
 */

/*@ requires numRow > 0 && numCol >0;
  @ requires \valid(loc + (0 .. numRow));
  @ requires \valid(idx + (0 .. numRow));
  @ requires 0<= localRow < numRow;
  @ assigns  a[0 .. localRow * numCol], idx[0 .. numRow], 
  @          loc[0 .. numRow];
  @ \mpi_collective[p2p, MPI_COMM_WORLD]:
  @   requires \mpi_valid(a, MPI_LONG_DOUBLE, numCol * localRow);
  @   requires \sum(0, \mpi_comm_size, (\lambda int k; 
  @                      \remote(localRow, k))) == numRow;                        // Requires each process holds a few rows of data
  @   requires \forall int i; 0 <= i < numRow ==>                                 
  @                           idx[i] == i && loc[i] == i;                         // loc and idx have initial values 
  @   ensure \forall int i, j; 0 <= i < numRow && 0 <= j < i                      // Ensures that the matrix a is already done
  @            ==> \let owner = ((nprocs*(idx[i]+1)-1)/numRow);                   // gaussian elimination.
  @                \remote(a, owner)[numCol * (idx[i] - first) + i] == 1 
  @                && 
  @                \remote(a, owner)[numCol * (idx[i] - first) + j] == 0;
  @   ensures \forall int i; 0 <= i < numRow ==>                                 
  @                    \exists int j; 0 <= j < numRow ==>                         // Ensures that loc is valid, i.e. each cell in loc has 
  @                            loc[j] == i;                                       // a unique value in [0, numRow).
  @   ensures \forall int i; 0 <= i < numRow ==>                                 
  @                    \exists int j; 0 <= j < numRow ==>                         // Ensures that idx is valid, i.e. each cell in idx has 
  @                            idx[j] == i;                                       // a unique value in [0, numRow).
  @   ensures \forall int i; 0 <= i < numRow ==>                                  
  @                           i == loc[idx[i]];                                   // Ensures that loc[i] = j, then idx[j] = i;
  @*/
void gaussianElimination(long double *a) {
  /* Buffer for the current toppest unprocessed row. */
  long double top[numCol];

  /* For each row of the matrix, it will be processed once. */
  for(int i=0; i < numRow; i++) {
    /* owner of the current unprocessed top row */
    int owner = OWNER(idx[i]); 
    /* the column of the next leading 1, initial value is numCol 
     * because later it will pick up a minimum number.
     */
    int leadCol = numCol; 
    /* the global index of the row the next leading 1 will be in */
    int rowOfLeadCol = numRow - 1;
    int rowOfLeadColOwner;    // the owner of rowOfLeadCol
    /* message buffer: [0]:leadCol ;[1]:rowOfLeadCol */
    int sendbuf[2];
    /* receive buffer: it will contain lead 1 column candidates from
       all processes */
    int recvbuf[2*nprocs];   
    int tmp;

    //step 1: find out the local leftmost nonzero column
    for(int j=i; j < numCol; j++) {
      int k, minLoc = numRow - 1;

      for(k = first; k < first + localRow; k++) {
        // only look at unprocessed rows
        if(loc[k] >= i && loc[k] <= minLoc) {
          if(a[(k-first)*numCol+j] != 0.0) {
            leadCol = j;
            rowOfLeadCol = k; 
	    minLoc = loc[k];
          }
        }
      }
      if(leadCol < numCol)
        break;
    }
    sendbuf[0] = leadCol;
    sendbuf[1] = loc[rowOfLeadCol];
    /* All reduce the smallest column(left-most) of leading 1 to every
       process */
    MPI_Allreduce(sendbuf, recvbuf, 1, MPI_2INT, MPI_MINLOC, MPI_COMM_WORLD);
    leadCol = recvbuf[0];
    rowOfLeadCol = idx[recvbuf[1]];
    /* Now the row containing next leading 1 is decided, findout the
       owner of it. */
    rowOfLeadColOwner = OWNER(rowOfLeadCol);
    /* if leadCol is still initial value, it means there is no avaliable 
       column suitable for next leading 1. */
    if(leadCol == numCol)
     return;
    // step 2: reducing the leading number to 1
    if(rank == rowOfLeadColOwner) {
      long double denom = a[(rowOfLeadCol - first)*numCol + leadCol];

      if(denom != 0.0)
        for(int j=leadCol; j < numCol; j++)
          a[(rowOfLeadCol - first)*numCol + j] = a[(rowOfLeadCol - first)*numCol + j] / denom;
      memcpy(top, &a[(rowOfLeadCol - first)*numCol
                     ], numCol*sizeof(long double));
    }
    MPI_Bcast(top, numCol, MPI_LONG_DOUBLE, rowOfLeadColOwner, MPI_COMM_WORLD);
    /* swap the row containing next leading 1 to the top location of
       current submatrix */
    if(loc[rowOfLeadCol] != i)
      setLoc(rowOfLeadCol, i);
    /* step 3: add a suitable value to all unprocessed rows to make
       all numbers at the same column as leading 1 zeros. */
    for(int j=0; j < localRow; j++) {
      if(loc[j+first] > i){
        long double factor = -a[j*numCol + leadCol];

        for(int k=leadCol; k < numCol; k++) {
          a[j*numCol + k] += factor * top[k];
        }
      }
    }
  }
}



/* Perform a backward reduction on the given matrix which transforms a
   row echelon form to a reduced row echelon form */

/*@ requires \valid(loc + (0 .. numRow));
  @ requires \valid(idx + (0 .. numRow));
  @ requires 0<= localRow < numRow;
  @ requires numRow > 0 && numCol >0;
  @ assigns  a[0 .. localRow * numCol];
  @ \mpi_collective[P2P, MPI_COMM_WORLD]:
  @   requires \mpi_valid(a, MPI_LONG_DOUBLE, numCol * localRow);
  @   requires \sum(0, \mpi_comm_size, (\lambda int k; 
  @                      \remote(localRow, k))) == numRow;                        // Requires each process holds a few rows of data
  @   requires \forall int i; 0 <= i < numRow ==>                                 
  @                    \exists int j; 0 <= j < numRow ==>                         // loc is valid, i.e. each cell in loc has 
  @                            loc[j] == i;                                       // a unique value in [0, numRow).
  @   requires \forall int i; 0 <= i < numRow ==>                                 
  @                    \exists int j; 0 <= j < numRow ==>                         // idx is valid, i.e. each cell in idx has 
  @                            idx[j] == i;                                       // a unique value in [0, numRow).
  @   requires \forall int i; 0 <= i < numRow ==>                                 // If loc[i] = j, then idx[j] = i;
  @                           i == loc[idx[i]]; 
  @   requires \forall int i, j; 0 <= i < numRow && 0 <= j < i                    // Requires that the matrix a is already done
  @            ==> \let owner = ((nprocs*(idx[i]+1)-1)/numRow);                   // gaussian elimination.
  @                \remote(a, owner)[numCol * (idx[i] - first) + i] == 1 
  @                && 
  @                \remote(a, owner)[numCol * (idx[i] - first) + j] == 0;
  @   ensures  \forall int i,j; 0 <= i < numRow && 
  @                             0 <= j < numCol-1 && i != j                       // Ensures the result is in row-echlon form
  @            ==> \let owner = ((nprocs*(idx[i]+1)-1)/numRow);
  @                \remote(a, owner)[numCol * (idx[i] - first) + i] == 1;
  @                && 
  @                \remote(a, owner)[numCol * (idx[i] - first) + j] == 0;
*/
void backwardReduce(long double *a) {
  int leadCol;
  int owner;
  int i;
  long double top[numCol];

  i = (numRow > (numCol - 1))?(numCol-2):numRow-1;
  for(; i>=1; i--) {
    leadCol = -1;
    owner = OWNER(idx[i]);
    if(rank == owner)
      memcpy(top, &a[(idx[i] - first)*numCol + i], (numCol-i)*sizeof(long double));
    MPI_Bcast(top, (numCol-i), MPI_LONG_DOUBLE, owner, MPI_COMM_WORLD);
    //find out the leading 1 column
    for(int j=0; j<(numCol-i); j++){
      if(top[j] != 0.0){
	leadCol = j+i;
	break;
      }
    }
    if(leadCol == -1)
      continue;
    else {
      for(int j=first; j<first+localRow; j++){
	if(loc[j] < i){
	  long double factor = -a[(j-first)*numCol + leadCol];

	  for(int k=leadCol; k<numCol; k++)
	    a[(j-first)*numCol + k] += factor*top[k-i];
	}
      }
    }
  }
}
