
// Specification: dense matrix



// from csr_matrix.h:
typedef struct {
  double  *data;
  int     *i;
  int     *j;
  int      num_rows;
  int      num_cols;
  int      num_nonzeros;
} hypre_CSRMatrix;


hypre_CSRMatrix *
hypre_CSRMatrixCreate( int num_rows,
                       int num_cols,
                       int num_nonzeros )
{
   hypre_CSRMatrix  *matrix =
     (hypre_CSRMatrix *) malloc(sizeof(hypre_CSRMatrix));
   matrix->data = NULL;
   matrix->i = NULL;
   matrix->j = NULL;
   matrix->num_rows = num_rows;
   matrix->num_cols = num_cols;
   matrix->num_nonzeros = num_nonzeros;
   return matrix;
}


int 
hypre_CSRMatrixInitialize( hypre_CSRMatrix *matrix )
{
  int  num_rows     = matrix->num_rows;
  int  num_nonzeros = matrix->num_nonzeros;
  
  matrix->data = (double*)malloc(num_nonzeros*sizeof(double));
  matrix->i = (int*)malloc((num_rows + 1)*sizeof(int));
  matrix->j = (int*)malloc(num_nonzeros*sizeof(int));
  return 0;
}


void free_CSR( hypre_CSRMatrix *matrix ) {
  free(matrix->data);
  free(matrix->i);
  free(matrix->j);
  free(matrix);
}

hypre_CSRMatrix *
hypre_CSRMatrixAdd( hypre_CSRMatrix *A, hypre_CSRMatrix *B) {
  double     *A_data   = A->data;
  int        *A_i      = A->i;
  int        *A_j      = A->j;
  int         nrows_A  = A->num_rows;
  int         ncols_A  = A->num_cols;
  double     *B_data   = N->data;
  int        *B_i      = B->i;
  int        *B_j      = B->j;
  int         nrows_B  = B->num_rows;
  int         ncols_B  = B->num_cols;
  hypre_CSRMatrix *C;
  double     *C_data;
  int	      *C_i;
  int        *C_j;
  int         ia, ib, ic, jcol, num_nonzeros;
  int	       pos;
  int         *marker;

  marker = (int*)malloc(ncols_A*sizeof(int));
  C_i = (int*)malloc((nrows_A+1)*sizeof(int));
  for (ia = 0; ia < ncols_A; ia++)
    marker[ia] = -1;
  num_nonzeros = 0;
  C_i[0] = 0;
  for (ic = 0; ic < nrows_A; ic++) {
    for (ia = A_i[ic]; ia < A_i[ic+1]; ia++) {
      jcol = A_j[ia];
      marker[jcol] = ic;
      num_nonzeros++;
    }
    for (ib = B_i[ic]; ib < B_i[ic+1]; ib++) {
      jcol = B_j[ib];
      if (marker[jcol] != ic) {
	marker[jcol] = ic;
	num_nonzeros++;
      }
    }
    C_i[ic+1] = num_nonzeros;
  }

  C = hypre_CSRMatrixCreate(nrows_A, ncols_A, num_nonzeros);
  C->i = C_i;
  hypre_CSRMatrixInitialize(C);
  C_j = C->j;
  C_data = C->data;

  for (ia = 0; ia < ncols_A; ia++)
    marker[ia] = -1;
  pos = 0;

  /*
#pragma TASS joint invariant ic==spec.i;
#pragma TASS joint invariant						\
  forall {int i | 0<=i<ic}						\
  forall {int j | 0<=j<ncols_A}						\
  spec.C[i][j] = (exists k.(C_i[i]<=k && k<C_i[i+1] && j=C_j[k])) ? C_data[k] : 0.;
  */

  for (ic = 0; ic < nrows_A; ic++) {
    for (ia = A_i[ic]; ia < A_i[ic+1]; ia++) {
      jcol = A_j[ia];
      C_j[pos] = jcol;
      C_data[pos] = A_data[ia];
      marker[jcol] = pos;
      pos++;
    }
    for (ib = B_i[ic]; ib < B_i[ic+1]; ib++) {
      jcol = B_j[ib];
      if (marker[jcol] < C_i[ic]) {
	C_j[pos] = jcol;
	C_data[pos] = B_data[ib];
	marker[jcol] = pos;
	pos++;
      }
      else {
	C_data[marker[jcol]] += B_data[ib];
      }
    }
  }
  free(marker);
  return C;
}


