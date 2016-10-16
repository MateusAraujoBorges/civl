#include <mpi.h>
#ifdef _CIVL
#include <stdlib.h>
#include <civlc.cvh>
#endif

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

/*@ requires valid_vec(x) && valid_vec(y) && x->size==y->size;
  @ ensures \result == \sum(i=0..x->size-1) x->data[i]*y->data[i];
  @*/
double hypre_SeqVectorInnerProd(hypre_Vector *x, hypre_Vector *y) {
   double  *x_data = hypre_VectorData(x);
   double  *y_data = hypre_VectorData(y);
   int      size   = hypre_VectorSize(x);
   int      i;
   double   result = 0.0;

   size *= hypre_VectorNumVectors(x);

#ifdef HYPRE_USING_OPENMP
#pragma omp parallel for private(i) reduction(+:result) schedule(static)
#endif
   /*@ loop invariant i <= size &&
     @   result = \sum(j=0..i-1) y_data[j]*x_data[j];
     @ assigns result;
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

#define total_size(vec) ((vec)->size * (vec)->num_vectors)

/*@ predicate valid_vec(hypre_Vector *v) =
  @      \valid(v) && v->size >= 0
  @   && \valid(v->data[0..v->size-1]);
  @
  @ predicate compat_vec(hypre_Vector *u, hypre_Vector *v) =
  @      u->size == v->size && u->num_vectors == v->num_vectors;
  @
  @ predicate valid_par(hypre_ParVector *x) =
  @      \valid(x) && valid_vec(x->local_vector)
  @   && x->global_size == \on(0, x->global_size)
  @   && x->comm->gcomm == \on(0, x->comm->gcomm)
  @   && x->global_size == \sum(r=0..x->comm->size-1)
  @                        \on(r, x->local_vector->size);
  @
  @ predicate compat_par(hypre_ParVector *x, hypre_ParVector *y) =
  @      x->comm == y->comm
  @   && x->global_size == y->global_size
  @   && compat_vec(x->local_vector, y->local_vector);
  @*/
   

/*@ \mpi_collective[x->comm]:
  @   requires \valid_par(x) && \valid_par(y) && compat_par(x,y);
  @   requires x->local_vector->num_vectors == 1;
  @   ensures \result == 
  @     \sum(r=0..x->comm->size-1)
  @       \on(r, \sum(i = 0 .. x->local_vector->size - 1)
  @           x->local_vector->data[i] * y->local_vector->data[i]);
  @   assigns \nothing;
  @*/
double hypre_ParVectorInnerProd(hypre_ParVector *x, hypre_ParVector *y) {
   MPI_Comm      comm    = hypre_ParVectorComm(x);
   hypre_Vector *x_local = hypre_ParVectorLocalVector(x);
   hypre_Vector *y_local = hypre_ParVectorLocalVector(y);
   double result = 0.0;
   double local_result = hypre_SeqVectorInnerProd(x_local, y_local);
   
   MPI_Allreduce(&local_result, &result, 1, MPI_DOUBLE, MPI_SUM, comm);
   return result;
}


/* Stripped down driver for AMG2013 parallel inner product routine. */
#define XVET  x.local_vector
#define YVET  y.local_vector

#ifdef _CIVL
$input int VECTOR_LENGTH;
$assume(0 <= VECTOR_LENGTH && VECTOR_LENGTH < 10);
#endif
int main() {
  hypre_ParVector x, y;
  int nprocs;

  MPI_Init(NULL, NULL);
  MPI_Comm_size(MPI_COMM_WORLD, &nprocs);
#ifdef _CIVL
  x.comm = MPI_COMM_WORLD;
  y.comm = MPI_COMM_WORLD;
  XVET = (hypre_Vector *)malloc(sizeof(hypre_Vector));
  YVET = (hypre_Vector *)malloc(sizeof(hypre_Vector));
  XVET->data = (double *)malloc(sizeof(double) * VECTOR_LENGTH * nprocs);
  YVET->data = (double *)malloc(sizeof(double) * VECTOR_LENGTH * nprocs);
  XVET->size = VECTOR_LENGTH;
  YVET->size = VECTOR_LENGTH;
  XVET->num_vectors = nprocs;
  YVET->num_vectors = nprocs;
#endif
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
