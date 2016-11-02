#include <stdlib.h>
#include <stdio.h>

/*--------------------------------------------------------------------------
 * Preliminaries for the CSR and Dense Matrix structure
 *--------------------------------------------------------------------------*/
// from csr_matrix.h:
typedef struct {
    double  *data;
    int     *i;
    int     *j;
    int      num_rows;
    int      num_cols;
    int      num_nonzeros;
    
    /* for compressing rows in matrix multiplication  */
    int     *rownnz;
    int      num_rownnz;
    
    /* Does the CSRMatrix create/destroy `data', `i', `j'? */
    int      owns_data;
} hypre_CSRMatrix;

typedef struct {
    double  **data;
    int      num_rows;
    int      num_cols;
} DenseMatrix;

// from hyper_memory.c.
// Somewhat simplified by sfs to remove call to hyper_error.
char * hypre_CAlloc( int count, int elt_size ) {
    char *ptr;
    int   size = count*elt_size;
    
    if (size > 0) {
        ptr = calloc(count, elt_size);
    } else {
        ptr = NULL;
    }
    return ptr;
}

// from hyper_memory.c:
void
hypre_Free( char *ptr )
{
    if (ptr)
    {
#ifdef HYPRE_USE_UMALLOC
        int threadid = hypre_GetThreadID();
        
        _ufree_(ptr);
#else
        free(ptr);
#endif
    }
}

// from hypre_memory.h:
#define hypre_CTAlloc(type, count) \
( (type *)hypre_CAlloc((unsigned int)(count), (unsigned int)sizeof(type)) )
#define hypre_TFree(ptr) \
( hypre_Free((char *)ptr), ptr = NULL )

/*--------------------------------------------------------------------------
 * Accessor functions for the CSR Matrix structure
 *--------------------------------------------------------------------------*/

#define hypre_CSRMatrixData(matrix)         ((matrix) -> data)
#define hypre_CSRMatrixI(matrix)            ((matrix) -> i)
#define hypre_CSRMatrixJ(matrix)            ((matrix) -> j)
#define hypre_CSRMatrixNumRows(matrix)      ((matrix) -> num_rows)
#define hypre_CSRMatrixNumCols(matrix)      ((matrix) -> num_cols)
#define hypre_CSRMatrixNumNonzeros(matrix)  ((matrix) -> num_nonzeros)
#define hypre_CSRMatrixRownnz(matrix)       ((matrix) -> rownnz)
#define hypre_CSRMatrixNumRownnz(matrix)    ((matrix) -> num_rownnz)
#define hypre_CSRMatrixOwnsData(matrix)     ((matrix) -> owns_data)
#define DenseMatrixData(matrix)         ((matrix) -> data)
#define DenseMatrixNumRows(matrix)      ((matrix) -> num_rows)
#define DenseMatrixNumCols(matrix)      ((matrix) -> num_cols)
#define DenseMatrixOwnsData(matrix)     ((matrix) -> owns_data)


// from csr_matop.c:
hypre_CSRMatrix *
hypre_CSRMatrixCreate( int num_rows,
                       int num_cols,
                       int num_nonzeros )
{
   hypre_CSRMatrix  *matrix;

   matrix = hypre_CTAlloc(hypre_CSRMatrix, 1);

   hypre_CSRMatrixData(matrix) = NULL;
   hypre_CSRMatrixI(matrix)    = NULL;
   hypre_CSRMatrixJ(matrix)    = NULL;
   hypre_CSRMatrixRownnz(matrix) = NULL;
   hypre_CSRMatrixNumRows(matrix) = num_rows;
   hypre_CSRMatrixNumCols(matrix) = num_cols;
   hypre_CSRMatrixNumNonzeros(matrix) = num_nonzeros;

   /* set defaults */
   hypre_CSRMatrixOwnsData(matrix) = 1;
   hypre_CSRMatrixNumRownnz(matrix) = num_rows;
   
   return matrix;
}

// Created based on `hypre_CSRMatrixCreate' from csr_matop.c:
DenseMatrix *
DenseMatrixCreate( int num_rows,
                        int num_cols)
{
    DenseMatrix  *matrix;
    
    matrix = hypre_CTAlloc(DenseMatrix, 1);
    //TODO: Change all hypre things for dense to malloc
    
    DenseMatrixData(matrix) = NULL;
    DenseMatrixNumRows(matrix) = num_rows;
    DenseMatrixNumCols(matrix) = num_cols;
    return matrix;
}


// from csr_matop.c:
int
hypre_CSRMatrixInitialize( hypre_CSRMatrix *matrix )
{
   int  num_rows     = hypre_CSRMatrixNumRows(matrix);
   int  num_nonzeros = hypre_CSRMatrixNumNonzeros(matrix);
   int  ierr=0;
   

   if ( ! hypre_CSRMatrixData(matrix) && num_nonzeros )
      hypre_CSRMatrixData(matrix) = hypre_CTAlloc(double, num_nonzeros);
   if ( ! hypre_CSRMatrixI(matrix) )
      hypre_CSRMatrixI(matrix)    = hypre_CTAlloc(int, num_rows + 1);
   if ( ! hypre_CSRMatrixJ(matrix) && num_nonzeros )
      hypre_CSRMatrixJ(matrix)    = hypre_CTAlloc(int, num_nonzeros);

   return ierr;
}

// Created based on `hypre_CSRMatrixInitialize' from csr_matop.c:
int
DenseMatrixInitialize( DenseMatrix *matrix )
{
    int  num_rows     = hypre_CSRMatrixNumRows(matrix);
    int  num_cols     = hypre_CSRMatrixNumCols(matrix);
    int  ierr=0;
    
    if (! DenseMatrixData(matrix)) {
        DenseMatrixData(matrix) = hypre_CTAlloc(double*, num_rows);
        for (int i = 0; i < num_rows; i ++)
            DenseMatrixData(matrix)[i] = hypre_CTAlloc(double, num_cols);
    }
    
    return ierr;
}


// from csr_matop.c:
hypre_CSRMatrix *
hypre_CSRMatrixAdd( hypre_CSRMatrix *A, hypre_CSRMatrix *B) {
  double     *A_data   = hypre_CSRMatrixData(A);
  int        *A_i      = hypre_CSRMatrixI(A);
  int        *A_j      = hypre_CSRMatrixJ(A);
  int         nrows_A  = hypre_CSRMatrixNumRows(A);
  int         ncols_A  = hypre_CSRMatrixNumCols(A);
  double     *B_data   = hypre_CSRMatrixData(B);
  int        *B_i      = hypre_CSRMatrixI(B);
  int        *B_j      = hypre_CSRMatrixJ(B);
  int         nrows_B  = hypre_CSRMatrixNumRows(B);
  int         ncols_B  = hypre_CSRMatrixNumCols(B);
  hypre_CSRMatrix *C;
  double     *C_data;
  int	      *C_i;
  int        *C_j;
  int         ia, ib, ic, jcol, num_nonzeros;
  int	       pos;
  int         *marker;

  marker = hypre_CTAlloc(int, ncols_A);
  C_i = hypre_CTAlloc(int, nrows_A+1);
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
  hypre_CSRMatrixI(C) = C_i;
  hypre_CSRMatrixInitialize(C);
  C_j = hypre_CSRMatrixJ(C);
  C_data = hypre_CSRMatrixData(C);

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
  hypre_TFree(marker);
  return C;
}

// Created based on `hypre_CSRMatrixAdd' from csr_matop.c:
DenseMatrix *
DenseMatrixAdd( DenseMatrix *A, DenseMatrix *B) {
    double     **A_data   = DenseMatrixData(A);
    int         nrows_A  = DenseMatrixNumRows(A);
    int         ncols_A  = DenseMatrixNumCols(A);
    double     **B_data   = DenseMatrixData(B);
    int         nrows_B  = DenseMatrixNumRows(B);
    int         ncols_B  = DenseMatrixNumCols(B);
    double     **C_data;
    DenseMatrix *C;
    int         ic, jc;
    
    
    /*
     #pragma TASS joint invariant ic==spec.i;
     #pragma TASS joint invariant						\
     forall {int i | 0<=i<ic}						\
     forall {int j | 0<=j<ncols_A}						\
     spec.C[i][j] = (exists k.(C_i[i]<=k && k<C_i[i+1] && j=C_j[k])) ? C_data[k] : 0.;
     */
    
    for (ic = 0; ic < nrows_A; ic++){
        for (jc = 0; jc < ncols_A; jc++){
            C_data[ic][jc] = A_data[ic][jc] + B_data[ic][jc];
        }
    }
    return C;
}

DenseMatrix *
hypre_CSR2Dense(hypre_CSRMatrix *C) {
    double     *C_data   = hypre_CSRMatrixData(C);
    int        *C_i      = hypre_CSRMatrixI(C);
    int        *C_j      = hypre_CSRMatrixJ(C);
    int         nrows_C  = hypre_CSRMatrixNumRows(C);
    int         ncols_C  = hypre_CSRMatrixNumCols(C);
    int ic, jc, c_col, num_nonzeros;
    DenseMatrix *D = DenseMatrixCreate(nrows_C, ncols_C);
    
    DenseMatrixInitialize(D);
    for (ic = 0; ic < nrows_C; ic++) {
        for (jc = C_i[ic]; jc < C_i[ic+1]; jc++) {
            DenseMatrixData(D)[ic][jc] = C_data[jc];
        }
    }
    return D;
}

/*--------------------------------------------------------------------------
 * Preliminaries for the CSR and Dense Matrix structure
 *--------------------------------------------------------------------------*/

DenseMatrix *expand_then_add(hypre_CSRMatrix *C1, hypre_CSRMatrix * C2) {
    return DenseMatrixAdd(hypre_CSR2Dense(C1), hypre_CSR2Dense(C2));
}

DenseMatrix *add_then_expand(hypre_CSRMatrix *C1, hypre_CSRMatrix * C2) {
    return hypre_CSR2Dense(hypre_CSRMatrixAdd(C1, C2));
}

int main() {
    int nRow = 4;
    int nCol = 4;
    int nonZero = 16;
    
    printf("Creating Matrice .. \n");
    DenseMatrix *dnsMat_C1 = DenseMatrixCreate(nRow, nCol);
    DenseMatrix *dnsMat_C2 = DenseMatrixCreate(nRow, nCol);
    hypre_CSRMatrix *csrMat_A = hypre_CSRMatrixCreate(nRow, nCol, nonZero);
    hypre_CSRMatrix *csrMat_B = hypre_CSRMatrixCreate(nRow, nCol, nonZero);
    
    hypre_CSRMatrixInitialize(csrMat_A);
    hypre_CSRMatrixInitialize(csrMat_B);
    DenseMatrixInitialize(dnsMat_C1);
    DenseMatrixInitialize(dnsMat_C2);
    
//    dnsMat_C1 = expand_then_add(csrMat_A, csrMat_B);
//    dnsMat_C2 = add_then_expand(csrMat_A, csrMat_B);
    
    return 0;
}



