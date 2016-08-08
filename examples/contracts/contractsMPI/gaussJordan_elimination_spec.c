/* FILE: gaussJordan_elimination.c A gaussian-jordan elimination
 * solver that converts a given matrix to a reduce row echelon form
 * matrix
 * RUN : mpicc gaussJordan_elimination.c; mpiexec -n 4 ./a.out numRow numCol m[0][0], m[0][1] ...
 * VERIFY : civl verify gaussianJordan_elimination.c
 */
#include <mpi.h>
#include <stdlib.h>
#include <string.h>
#include <civlc.cvh>

$input int ROWB = 3;                      // upper bound of numRow
$input int numRow;                        // number of rows in the matrix
$assume(0 < numRow && numRow <= ROWB);
$input int COLB = 4;                      // upper bound of numCol
$input int numCol;                        // number of columns in the matrix
$assume(0 < numCol && numCol <= COLB && numCol > numRow);
$input long double data[numRow][numCol];  // input matrix

/*@ requires \valid(a + (0 .. (numCol * numRow)));
  @ requires \valid(rowLoc + (0 .. numRow));
  @ requires numRow > 0 && numCol >0;
  @ requires \forall int i; 0 <= i < numRow ==> rowLoc[i] = i;                 rowLoc has initial values
  @ assigns  a[0 .. numRow * numCol], rowLoc[0 .. numRow];
  @ ensures \forall int i, j; 0 <= i < numRow && 0 <= j < i                    // Requires that the matrix a is already done
  @        ==> a[numCol * i + i] == 1 && a[numCol * i + j] == 0;               // gaussian elimination.
  @ ensures \forall int i; 0 <= i < numRow ==>                                 
  @                  \exists int j; 0 <= j < numRow ==>                        // rowLoc is valid, i.e. each cell in rowLoc has 
  @                          rowLoc[j] == i;                                   // a unique value in [0, numRow).
  @
*/
void specElimination(long double *a, int * rowLoc) {
  long double denom;      // a temporary variable will be used to
                          //divide other variables

  for(int i=0; i < numRow; i++) {
    int leadCol = numCol; // the column where leading 1  be in
    int rowOfLeadCol = i; // the row where leadCol be in

    /* step 1: Find out the leftmost nonzero column, interchange it with
     the current iterated row. */
    for(int j=i; j < numCol; j++) {
      for(int k=i; k < numRow; k++) {
	if(a[rowLoc[k]*numCol + j] != 0.0) {
	  leadCol = j;
	  rowOfLeadCol = k;
	  break;
	}
      }
      if(leadCol < numCol) 
	break;
    }
    /* If there is no leading 1 in all unprocessed rows, elimination
       terminates. */
    if(leadCol == numCol)
      return;
    /* step 2: Reducing the leading number to one */
    denom = a[rowLoc[rowOfLeadCol]*numCol + leadCol];
    /* If the denominator is zero (or extremely nearing zero), do
     * nothing.  The reason is the denominator is the left-most
     * nonzero element in all unprocessed rows, if it's zero, all
     * numbers at that column in all unprocessed rows are zeros. For
     * such a case, it's no need to do anything in this iteration.
     */
    if(denom != 0.0) {
      for(int j=leadCol; j < numCol; j++) {
	long double tmp = a[rowLoc[rowOfLeadCol]*numCol + j] / denom;

	a[rowLoc[rowOfLeadCol]*numCol + j] = tmp;
      }
    }
    if(rowOfLeadCol != i) {
      int tmp;
      
      tmp = rowLoc[i];
      rowLoc[i] = rowLoc[rowOfLeadCol];
      rowLoc[rowOfLeadCol] = tmp;
    }
    /* step 3: Add a suitable value to each row below row i so that they have zero at column i */
    for(int j=i+1; j < numRow; j++) {
      long double factor = -a[rowLoc[j]*numCol + leadCol];

      for(int k=leadCol; k < numCol; k++)
	a[rowLoc[j]*numCol + k] += factor * a[rowLoc[i]*numCol + k];
    }
  }
}

/* Working upward to make each leading one the only nonzero number in
 * which column it be .
 * Parameters:
 * a: the matrix in a row echelon form.
 * rowLoc: a look-up table for rows' locations
 */
/*@ requires \valid(a + (0 .. (numCol * numRow)));
  @ requires \valid(rowLoc + (0 .. numRow));
  @ requires numRow > 0 && numCol >0;
  @ requires \forall int i, j; 0 <= i < numRow && 0 <= j < i                    // Requires that the matrix a is already done
  @        ==> a[numCol * i + i] == 1 && a[numCol * i + j] == 0;                // gaussian elimination.
  @ requires \forall int i; 0 <= i < numRow ==>                                 
  @                  \exists int j; 0 <= j < numRow ==>                         // rowLoc is valid, i.e. each cell in rowLoc has 
  @                          rowLoc[j] == i;                                    // a unique value in [0, numRow).
  @ assigns  a[0 .. numRow * numCol];
  @ ensures  \forall int i,j; 0 <= i < numRow && 
  @                           0 <= j < numCol-1 && i != j                       // Ensures the result is in row-echlon form
  @   ==> a[numCol * i + i] == 1 && a[numCol * i + j] == 0;
  @ 
  @
*/
void specReduce(long double * a, int * rowLoc) {
  int leadCol;  // the column of the leading one in a row
  int i;

  i = (numRow > (numCol - 1))?(numCol-2):(numRow-1);
  for(; i>=0; i--) {
    //Find the leading 1, but if it's an all-zero row, skip it.
    leadCol = -1;
    for(int j=i; j<numCol; j++) {
      if(a[rowLoc[i]*numCol + j] != 0.0) {
	leadCol = j;
	break;
      }
    }
    // if it's not an all-zero row, reducing all other numbers in all
    // rows above at the column at where the leading 1 be.
    if(leadCol > -1) {
      for(int j=i-1; j >=0; j--) {
	long double factor = -a[rowLoc[j]*numCol + leadCol];

	for(int k=leadCol; k < numCol; k++) 
	  a[rowLoc[j]*numCol + k] += a[rowLoc[i]*numCol + k] * factor;
      }
    }
  }
}
