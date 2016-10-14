
#include <mpi.h>
#define HYPRE_BigInt int

// seq_mv.h :

typedef struct
{
   double  *data;
   int      size;

   /* Does the Vector create/destroy `data'? */
   int      owns_data;

   /* For multivectors...*/
   int   num_vectors;  /* the above "size" is size of one vector */
   int   multivec_storage_method;
   /* ...if 0, store colwise v0[0], v0[1], ..., v1[0], v1[1], ... v2[0]... */
   /* ...if 1, store rowwise v0[0], v1[0], ..., v0[1], v1[1], ... */
   /* With colwise storage, vj[i] = data[ j*size + i]
      With rowwise storage, vj[i] = data[ j + num_vectors*i] */
   int  vecstride, idxstride;
   /* ... so vj[i] = data[ j*vecstride + i*idxstride ] regardless of row_storage.*/

} hypre_Vector;

#define hypre_VectorData(vector)      ((vector) -> data)
#define hypre_VectorSize(vector)      ((vector) -> size)
#define hypre_VectorOwnsData(vector)  ((vector) -> owns_data)
#define hypre_VectorNumVectors(vector) ((vector) -> num_vectors)
#define hypre_VectorMultiVecStorageMethod(vector) ((vector) -> multivec_storage_method)
#define hypre_VectorVectorStride(vector) ((vector) -> vecstride )
#define hypre_VectorIndexStride(vector) ((vector) -> idxstride )


// vector.c :

double   hypre_SeqVectorInnerProd( hypre_Vector *x,
                          hypre_Vector *y )
{
   double  *x_data = hypre_VectorData(x);
   double  *y_data = hypre_VectorData(y);
   int      size   = hypre_VectorSize(x);
           
   int      i;

   double      result = 0.0;

   size *=hypre_VectorNumVectors(x);

#ifdef HYPRE_USING_OPENMP
#pragma omp parallel for private(i) reduction(+:result) schedule(static)
#endif
   for (i = 0; i < size; i++)
      result += y_data[i] * x_data[i];

   return result;
}


// parcsr_mv.h:

typedef struct
{
   int                   length;
   HYPRE_BigInt          row_start;
   HYPRE_BigInt          row_end;
   int                   storage_length;
   int                   *proc_list;
   HYPRE_BigInt	         *row_start_list;
   HYPRE_BigInt          *row_end_list;  
  int                    *sort_index;
} hypre_IJAssumedPart;


typedef struct
{
   MPI_Comm	 comm;

   HYPRE_BigInt  global_size;
   HYPRE_BigInt  first_index;
   HYPRE_BigInt  last_index;
   HYPRE_BigInt *partitioning;
   hypre_Vector	*local_vector; 

   int      	 owns_data;
   int      	 owns_partitioning;

   hypre_IJAssumedPart *assumed_partition; 
} hypre_ParVector;


#define hypre_ParVectorComm(vector)  	        ((vector) -> comm)
#define hypre_ParVectorGlobalSize(vector)       ((vector) -> global_size)
#define hypre_ParVectorFirstIndex(vector)       ((vector) -> first_index)
#define hypre_ParVectorLastIndex(vector)        ((vector) -> last_index)
#define hypre_ParVectorPartitioning(vector)     ((vector) -> partitioning)
#define hypre_ParVectorLocalVector(vector)      ((vector) -> local_vector)
#define hypre_ParVectorOwnsData(vector)         ((vector) -> owns_data)
#define hypre_ParVectorOwnsPartitioning(vector) ((vector) -> owns_partitioning)
#define hypre_ParVectorNumVectors(vector)\
 (hypre_VectorNumVectors( hypre_ParVectorLocalVector(vector) ))

#define hypre_ParVectorAssumedPartition(vector) ((vector) -> assumed_partition)


// par_vector.c :

double
hypre_ParVectorInnerProd( hypre_ParVector *x,
                    hypre_ParVector *y )
{
   MPI_Comm      comm    = hypre_ParVectorComm(x);
   hypre_Vector *x_local = hypre_ParVectorLocalVector(x);
   hypre_Vector *y_local = hypre_ParVectorLocalVector(y);
           
   double result = 0.0;
   double local_result = hypre_SeqVectorInnerProd(x_local, y_local);
   
   MPI_Allreduce(&local_result, &result, 1, MPI_DOUBLE, MPI_SUM, comm);
   
   return result;
}


/* Stripped down driver for AMG2013 parallel inner product routine. */

int main() {
  hypre_ParVector x, y;
  double result = hypre_ParVectorInnerProd(&x, &y);
  return result != 0;
}
