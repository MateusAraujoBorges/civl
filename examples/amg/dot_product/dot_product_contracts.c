#include <mpi.h>
#include <stdlib.h>
#include <civlc.cvh>
#pragma PARSE_ACSL


#define HYPRE_BigInt int
#define INT_MAX      65536

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
#define VEC_SIZE(x) ((x)->size * (x)->num_vectors)
/*@ requires \valid(x) && \valid(y);
  @ requires \valid(x->data + (0 .. VEC_SIZE(x))) && \valid(y->data + (0 .. VEC_SIZE(y)));
  @ requires x->size == y->size;
  @ requires 0< x->size && x->size < INT_MAX;
  @ requires x->num_vectors == y->num_vectors;
  @ requires 0< x->num_vectors && x->num_vectors < INT_MAX;
  @ ensures \result == \sum(0, VEC_SIZE(x)-1, 
  @                            \lambda int t; x->data[t]*y->data[t]
  @                         );
  @*/
double hypre_SeqVectorInnerProd(hypre_Vector *x, hypre_Vector *y) {
   double  *x_data = hypre_VectorData(x);
   double  *y_data = hypre_VectorData(y);
   int      size   = hypre_VectorSize(x);
   int      i;
   double   result = 0.0;

   size *= hypre_VectorNumVectors(x);

   /*@ 
     @ loop invariant i >= 0 && i <= size && 
     @       result == \sum(0, i-1, \lambda int t; y_data[t] * x_data[t]);
     @*/
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

#define LOCAL_VECTOR(x)  ((x)->local_vector)

/*@ requires \valid(x) && \valid(y);
  @ requires \valid(x->local_vector) && \valid(y->local_vector);
  @ requires \valid(LOCAL_VECTOR(x)->data + (0 .. VEC_SIZE(LOCAL_VECTOR(x)))) &&
  @          \valid(LOCAL_VECTOR(y)->data + (0 .. VEC_SIZE(LOCAL_VECTOR(y))));
  @ requires LOCAL_VECTOR(x)->size == LOCAL_VECTOR(y)->size;
  @ requires 0< LOCAL_VECTOR(x)->size && LOCAL_VECTOR(x)->size < INT_MAX;
  @ requires LOCAL_VECTOR(x)->num_vectors == LOCAL_VECTOR(y)->num_vectors;
  @ requires 0< LOCAL_VECTOR(x)->num_vectors && LOCAL_VECTOR(x)->num_vectors < INT_MAX;
  @ \mpi_collective(MPI_COMM_WORLD, P2P):
  @    ensures \result ==  \sum(0, \mpi_comm_size-1, \lambda int p; \on(p,
  @                                                  \sum(0, VEC_SIZE(LOCAL_VECTOR(x))-1, 
  @                                                  \lambda int t; 
  @                                                  LOCAL_VECTOR(x)->data[t]*LOCAL_VECTOR(y)->data[t])
  @                                                                     )                   
  @                             );
  @   
  @*/
double hypre_ParVectorInnerProd(hypre_ParVector *x, hypre_ParVector *y) {
   MPI_Comm      comm    = hypre_ParVectorComm(x);
   hypre_Vector *x_local = hypre_ParVectorLocalVector(x);
   hypre_Vector *y_local = hypre_ParVectorLocalVector(y);
   double result = 0.0;
   double local_result = hypre_SeqVectorInnerProd(x_local, y_local);
   
   MPI_Allreduce(&local_result, &result, 1, MPI_DOUBLE, MPI_SUM, MPI_COMM_WORLD);
   return result;
}


/* Stripped down driver for AMG2013 parallel inner product routine. */
#define XVET  x.local_vector
#define YVET  y.local_vector

int main() {
  hypre_ParVector x, y;
  int nprocs;

  MPI_Init(NULL, NULL);
  MPI_Comm_size(MPI_COMM_WORLD, &nprocs);

  double result = hypre_ParVectorInnerProd(&x, &y);

  MPI_Finalize();
  free(XVET->data);
  free(YVET->data);
  free(XVET);
  free(YVET);
#ifdef DEBUG
  #include <stdio.h>
  printf("result = %f\n", result);
#endif
  return result != 0;
}
