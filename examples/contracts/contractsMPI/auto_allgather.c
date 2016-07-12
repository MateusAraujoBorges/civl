CIVL v1.7.1 of 2016-05-31 -- http://vsl.cis.udel.edu/civl
//========================== op.h ==========================
typedef enum Operation{
  _NO_OP,
  _MAX,
  _MIN,
  _SUM,
  _PROD,
  _LAND,
  _BAND,
  _LOR,
  _BOR,
  _LXOR,
  _BXOR,
  _MINLOC,
  _MAXLOC,
  _REPLACE
} Operation;
//========================== mpi.h =========================
typedef enum Operation MPI_Op;
typedef enum MPI_Datatype{
  MPI_CHAR,
  MPI_CHARACTER,
  MPI_SIGNED_CHAR,
  MPI_UNSIGNED_CHAR,
  MPI_BYTE,
  MPI_WCHAR,
  MPI_SHORT,
  MPI_UNSIGNED_SHORT,
  MPI_INT,
  MPI_INT16_T,
  MPI_INT32_T,
  MPI_INT64_T,
  MPI_INT8_T,
  MPI_INTEGER,
  MPI_INTEGER1,
  MPI_INTEGER16,
  MPI_INTEGER2,
  MPI_INTEGER4,
  MPI_INTEGER8,
  MPI_UNSIGNED,
  MPI_LONG,
  MPI_UNSIGNED_LONG,
  MPI_FLOAT,
  MPI_DOUBLE,
  MPI_LONG_DOUBLE,
  MPI_LONG_LONG_INT,
  MPI_UNSIGNED_LONG_LONG,
  MPI_LONG_LONG,
  MPI_PACKED,
  MPI_LB,
  MPI_UB,
  MPI_UINT16_T,
  MPI_UINT32_T,
  MPI_UINT64_T,
  MPI_UINT8_T,
  MPI_FLOAT_INT,
  MPI_DOUBLE_INT,
  MPI_LONG_INT,
  MPI_SHORT_INT,
  MPI_2INT,
  MPI_LONG_DOUBLE_INT,
  MPI_AINT,
  MPI_OFFSET,
  MPI_2DOUBLE_PRECISION,
  MPI_2INTEGER,
  MPI_2REAL,
  MPI_C_BOOL,
  MPI_C_COMPLEX,
  MPI_C_DOUBLE_COMPLEX,
  MPI_C_FLOAT_COMPLEX,
  MPI_C_LONG_DOUBLE_COMPLEX,
  MPI_COMPLEX,
  MPI_COMPLEX16,
  MPI_COMPLEX32,
  MPI_COMPLEX4,
  MPI_COMPLEX8,
  MPI_REAL,
  MPI_REAL16,
  MPI_REAL2,
  MPI_REAL4,
  MPI_REAL8
} MPI_Datatype;
typedef long MPI_Aint;
typedef int MPI_Fint;
typedef struct MPI_Comm MPI_Comm;
typedef struct MPI_Group MPI_Group;
typedef struct MPI_Request* MPI_Request;
typedef struct MPIX_Message MPIX_Message;
typedef struct MPI_File MPI_File;
typedef struct MPI_Errhandler MPI_Errhandler;
typedef struct MPI_User_function MPI_User_function;
typedef struct MPI_Copy_function MPI_Copy_function;
typedef struct MPI_Delete_function MPI_Delete_function;
typedef int MPI_Win;
typedef int MPI_Info;
typedef long long MPI_Offset;
typedef enum MPIR_Topo_type{
  MPI_GRAPH=1,
  MPI_CART=2,
  MPI_DIST_GRAPH=3
} MPIR_Topo_type;
typedef enum MPIR_Combiner_enum{
  MPI_COMBINER_NAMED=1,
  MPI_COMBINER_DUP=2,
  MPI_COMBINER_CONTIGUOUS=3,
  MPI_COMBINER_VECTOR=4,
  MPI_COMBINER_HVECTOR_INTEGER=5,
  MPI_COMBINER_HVECTOR=6,
  MPI_COMBINER_INDEXED=7,
  MPI_COMBINER_HINDEXED_INTEGER=8,
  MPI_COMBINER_HINDEXED=9,
  MPI_COMBINER_INDEXED_BLOCK=10,
  MPIX_COMBINER_HINDEXED_BLOCK=11,
  MPI_COMBINER_STRUCT_INTEGER=12,
  MPI_COMBINER_STRUCT=13,
  MPI_COMBINER_SUBARRAY=14,
  MPI_COMBINER_DARRAY=15,
  MPI_COMBINER_F90_REAL=16,
  MPI_COMBINER_F90_COMPLEX=17,
  MPI_COMBINER_F90_INTEGER=18,
  MPI_COMBINER_RESIZED=19
} MPIR_Combiner_enum;
typedef  (void (MPI_Comm*, int*)) MPI_Handler_function;
typedef  (int (MPI_Comm, int, void*, void*, void*, int*)) MPI_Comm_copy_attr_function;
typedef  (int (MPI_Comm, int, void*, void*)) MPI_Comm_delete_attr_function;
typedef  (int (MPI_Datatype, int, void*, void*, void*, int*)) MPI_Type_copy_attr_function;
typedef  (int (MPI_Datatype, int, void*, void*)) MPI_Type_delete_attr_function;
typedef  (int (MPI_Win, int, void*, void*, void*, int*)) MPI_Win_copy_attr_function;
typedef  (int (MPI_Win, int, void*, void*)) MPI_Win_delete_attr_function;
typedef  (void (MPI_Comm*, int*)) MPI_Comm_errhandler_function;
typedef  (void (MPI_File*, int*)) MPI_File_errhandler_function;
typedef  (void (MPI_Win*, int*)) MPI_Win_errhandler_function;
typedef MPI_Comm_errhandler_function MPI_Comm_errhandler_fn;
typedef MPI_File_errhandler_function MPI_File_errhandler_fn;
typedef MPI_Win_errhandler_function MPI_Win_errhandler_fn;
typedef  (int (void*, MPI_Datatype, int, void*, MPI_Offset, void*)) MPI_Datarep_conversion_function;
typedef  (int (MPI_Datatype datatype, MPI_Aint*, void*)) MPI_Datarep_extent_function;
typedef struct MPI_Status{
    int MPI_SOURCE;
    int MPI_TAG;
    int MPI_ERROR;
    int size;
} MPI_Status;
typedef  (int (void*, int)) MPI_Grequest_cancel_function;
typedef  (int (void*)) MPI_Grequest_free_function;
typedef  (int (void*, MPI_Status*)) MPI_Grequest_query_function;
MPI_Comm MPI_COMM_WORLD;
MPI_Comm MPI_COMM_SELF;
MPI_Comm MPI_COMM_PARENT;
MPI_Comm MPI_COMM_TYPE_SHARED;
int MPI_Send(void*, int, MPI_Datatype, int, int, MPI_Comm);
int MPI_Recv(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Status*);
int MPI_Get_count(MPI_Status*, MPI_Datatype, int*);
int MPI_Bsend(void*, int, MPI_Datatype, int, int, MPI_Comm);
int MPI_Ssend(void*, int, MPI_Datatype, int, int, MPI_Comm);
int MPI_Rsend(void*, int, MPI_Datatype, int, int, MPI_Comm);
int MPI_Buffer_attach(void*, int);
int MPI_Buffer_detach(void*, int*);
int MPI_Isend(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Ibsend(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Issend(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Irsend(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Irecv(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Wait(MPI_Request*, MPI_Status*);
int MPI_Test(MPI_Request*, int*, MPI_Status*);
int MPI_Request_free(MPI_Request*);
int MPI_Waitany(int, MPI_Request*, int*, MPI_Status*);
int MPI_Testany(int, MPI_Request*, int*, int*, MPI_Status*);
int MPI_Waitall(int, MPI_Request*, MPI_Status*);
int MPI_Testall(int, MPI_Request*, int*, MPI_Status*);
int MPI_Waitsome(int, MPI_Request*, int*, int*, MPI_Status*);
int MPI_Testsome(int, MPI_Request*, int*, int*, MPI_Status*);
int MPI_Iprobe(int, int, MPI_Comm, int*, MPI_Status*);
int MPI_Probe(int, int, MPI_Comm, MPI_Status*);
int MPI_Cancel(MPI_Request*);
int MPI_Test_cancelled(MPI_Status*, int*);
int MPI_Send_init(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Bsend_init(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Ssend_init(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Rsend_init(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Recv_init(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Start(MPI_Request*);
int MPI_Startall(int, MPI_Request*);
int MPI_Sendrecv(void*, int, MPI_Datatype, int, int, void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Status*);
int MPI_Sendrecv_replace(void*, int, MPI_Datatype, int, int, int, int, MPI_Comm, MPI_Status*);
int MPI_Type_contiguous(int, MPI_Datatype, MPI_Datatype*);
int MPI_Type_vector(int, int, int, MPI_Datatype, MPI_Datatype*);
int MPI_Type_hvector(int, int, MPI_Aint, MPI_Datatype, MPI_Datatype*);
int MPI_Type_indexed(int, int*, int*, MPI_Datatype, MPI_Datatype*);
int MPI_Type_hindexed(int, int*, MPI_Aint*, MPI_Datatype, MPI_Datatype*);
int MPI_Type_struct(int, int*, MPI_Aint*, MPI_Datatype*, MPI_Datatype*);
int MPI_Address(void*, MPI_Aint*);
int MPI_Type_extent(MPI_Datatype, MPI_Aint*);
int MPI_Type_size(MPI_Datatype, int*);
int MPI_Type_lb(MPI_Datatype, MPI_Aint*);
int MPI_Type_ub(MPI_Datatype, MPI_Aint*);
int MPI_Type_commit(MPI_Datatype*);
int MPI_Type_free(MPI_Datatype*);
int MPI_Get_elements(MPI_Status*, MPI_Datatype, int*);
int MPI_Pack(void*, int, MPI_Datatype, void*, int, int*, MPI_Comm);
int MPI_Unpack(void*, int, int*, void*, int, MPI_Datatype, MPI_Comm);
int MPI_Pack_size(int, MPI_Datatype, MPI_Comm, int*);
int MPI_Barrier(MPI_Comm);
int MPI_Bcast(void*, int, MPI_Datatype, int, MPI_Comm);
int MPI_Gather(void*, int, MPI_Datatype, void*, int, MPI_Datatype, int, MPI_Comm);
int MPI_Gatherv(void*, int, MPI_Datatype, void*, int*, int*, MPI_Datatype, int, MPI_Comm);
int MPI_Scatter(void*, int, MPI_Datatype, void*, int, MPI_Datatype, int, MPI_Comm);
int MPI_Scatterv(void*, int*, int*, MPI_Datatype, void*, int, MPI_Datatype, int, MPI_Comm);
int MPI_Allgather(void*, int, MPI_Datatype, void*, int, MPI_Datatype, MPI_Comm);
int MPI_Allgatherv(void*, int, MPI_Datatype, void*, int*, int*, MPI_Datatype, MPI_Comm);
int MPI_Alltoall(void*, int, MPI_Datatype, void*, int, MPI_Datatype, MPI_Comm);
int MPI_Alltoallv(void*, int*, int*, MPI_Datatype, void*, int*, int*, MPI_Datatype, MPI_Comm);
int MPI_Reduce(void*, void*, int, MPI_Datatype, MPI_Op, int, MPI_Comm);
int MPI_Op_create(MPI_User_function*, int, MPI_Op*);
int MPI_Op_free(MPI_Op*);
int MPI_Allreduce(void*, void*, int, MPI_Datatype, MPI_Op, MPI_Comm);
int MPI_Reduce_scatter(void*, void*, int*, MPI_Datatype, MPI_Op, MPI_Comm);
int MPI_Scan(void*, void*, int, MPI_Datatype, MPI_Op, MPI_Comm);
int MPI_Group_size(MPI_Group, int*);
int MPI_Group_rank(MPI_Group, int*);
int MPI_Group_translate_ranks(MPI_Group, int, int*, MPI_Group, int*);
int MPI_Group_compare(MPI_Group, MPI_Group, int*);
int MPI_Comm_group(MPI_Comm, MPI_Group*);
int MPI_Group_union(MPI_Group, MPI_Group, MPI_Group*);
int MPI_Group_intersection(MPI_Group, MPI_Group, MPI_Group*);
int MPI_Group_difference(MPI_Group, MPI_Group, MPI_Group*);
int MPI_Group_incl(MPI_Group, int, int*, MPI_Group*);
int MPI_Group_excl(MPI_Group, int, int*, MPI_Group*);
int MPI_Group_range_incl(MPI_Group, int, int [][3], MPI_Group*);
int MPI_Group_range_excl(MPI_Group, int, int [][3], MPI_Group*);
int MPI_Group_free(MPI_Group*);
int MPI_Comm_size(MPI_Comm, int*);
int MPI_Comm_rank(MPI_Comm, int*);
int MPI_Comm_compare(MPI_Comm, MPI_Comm, int*);
int MPI_Comm_dup(MPI_Comm, MPI_Comm*);
int MPI_Comm_create(MPI_Comm, MPI_Group, MPI_Comm*);
int MPI_Comm_split(MPI_Comm, int, int, MPI_Comm*);
int MPI_Comm_free(MPI_Comm*);
int MPI_Comm_test_inter(MPI_Comm, int*);
int MPI_Comm_remote_size(MPI_Comm, int*);
int MPI_Comm_remote_group(MPI_Comm, MPI_Group*);
int MPI_Intercomm_create(MPI_Comm, int, MPI_Comm, int, int, MPI_Comm*);
int MPI_Intercomm_merge(MPI_Comm, int, MPI_Comm*);
int MPI_Keyval_create(MPI_Copy_function*, MPI_Delete_function*, int*, void*);
int MPI_Keyval_free(int*);
int MPI_Attr_put(MPI_Comm, int, void*);
int MPI_Attr_get(MPI_Comm, int, void*, int*);
int MPI_Attr_delete(MPI_Comm, int);
int MPI_Topo_test(MPI_Comm, int*);
int MPI_Cart_create(MPI_Comm, int, int*, int*, int, MPI_Comm*);
int MPI_Dims_create(int, int, int*);
int MPI_Graph_create(MPI_Comm, int, int*, int*, int, MPI_Comm*);
int MPI_Graphdims_get(MPI_Comm, int*, int*);
int MPI_Graph_get(MPI_Comm, int, int, int*, int*);
int MPI_Cartdim_get(MPI_Comm, int*);
int MPI_Cart_get(MPI_Comm, int, int*, int*, int*);
int MPI_Cart_rank(MPI_Comm, int*, int*);
int MPI_Cart_coords(MPI_Comm, int, int, int*);
int MPI_Graph_neighbors_count(MPI_Comm, int, int*);
int MPI_Graph_neighbors(MPI_Comm, int, int, int*);
int MPI_Cart_shift(MPI_Comm, int, int, int*, int*);
int MPI_Cart_sub(MPI_Comm, int*, MPI_Comm*);
int MPI_Cart_map(MPI_Comm, int, int*, int*, int*);
int MPI_Graph_map(MPI_Comm, int, int*, int*, int*);
int MPI_Get_processor_name(char*, int*);
int MPI_Get_version(int*, int*);
int MPI_Errhandler_create(MPI_Handler_function*, MPI_Errhandler*);
int MPI_Errhandler_set(MPI_Comm, MPI_Errhandler);
int MPI_Errhandler_get(MPI_Comm, MPI_Errhandler*);
int MPI_Errhandler_free(MPI_Errhandler*);
int MPI_Error_string(int, char*, int*);
int MPI_Error_class(int, int*);
double MPI_Wtime(void);
double MPI_Wtick(void);
int MPI_Init(int*, char***);
int MPI_Finalize(void);
int MPI_Initialized(int*);
$system[mpi] int MPI_Abort(MPI_Comm, int);
int MPI_Pcontrol(const int, ...);
int MPI_DUP_FN(MPI_Comm, int, void*, void*, void*, int*);
int MPI_Close_port(char*);
int MPI_Comm_accept(char*, MPI_Info, int, MPI_Comm, MPI_Comm*);
int MPI_Comm_connect(char*, MPI_Info, int, MPI_Comm, MPI_Comm*);
int MPI_Comm_disconnect(MPI_Comm*);
int MPI_Comm_get_parent(MPI_Comm*);
int MPI_Comm_join(int, MPI_Comm*);
int MPI_Comm_spawn(char*, char* [], int, MPI_Info, int, MPI_Comm, MPI_Comm*, int []);
int MPI_Comm_spawn_multiple(int, char* [], char** [], int [], MPI_Info [], int, MPI_Comm, MPI_Comm*, int []);
int MPI_Lookup_name(char*, MPI_Info, char*);
int MPI_Open_port(MPI_Info, char*);
int MPI_Publish_name(char*, MPI_Info, char*);
int MPI_Unpublish_name(char*, MPI_Info, char*);
int MPI_Accumulate(void*, int, MPI_Datatype, int, MPI_Aint, int, MPI_Datatype, MPI_Op, MPI_Win);
int MPI_Get(void*, int, MPI_Datatype, int, MPI_Aint, int, MPI_Datatype, MPI_Win);
int MPI_Put(void*, int, MPI_Datatype, int, MPI_Aint, int, MPI_Datatype, MPI_Win);
int MPI_Win_complete(MPI_Win);
int MPI_Win_create(void*, MPI_Aint, int, MPI_Info, MPI_Comm, MPI_Win*);
int MPI_Win_fence(int, MPI_Win);
int MPI_Win_free(MPI_Win*);
int MPI_Win_get_group(MPI_Win, MPI_Group*);
int MPI_Win_lock(int, int, int, MPI_Win);
int MPI_Win_post(MPI_Group, int, MPI_Win);
int MPI_Win_start(MPI_Group, int, MPI_Win);
int MPI_Win_test(MPI_Win, int*);
int MPI_Win_unlock(int, MPI_Win);
int MPI_Win_wait(MPI_Win);
int MPI_Alltoallw(void*, int [], int [], MPI_Datatype [], void*, int [], int [], MPI_Datatype [], MPI_Comm);
int MPI_Exscan(void*, void*, int, MPI_Datatype, MPI_Op, MPI_Comm);
int MPI_Add_error_class(int*);
int MPI_Add_error_code(int, int*);
int MPI_Add_error_string(int, char*);
int MPI_Comm_call_errhandler(MPI_Comm, int);
int MPI_Comm_create_keyval(MPI_Comm_copy_attr_function*, MPI_Comm_delete_attr_function*, int*, void*);
int MPI_Comm_delete_attr(MPI_Comm, int);
int MPI_Comm_free_keyval(int*);
int MPI_Comm_get_attr(MPI_Comm, int, void*, int*);
int MPI_Comm_get_name(MPI_Comm, char*, int*);
int MPI_Comm_set_attr(MPI_Comm, int, void*);
int MPI_Comm_set_name(MPI_Comm, char*);
int MPI_File_call_errhandler(MPI_File, int);
int MPI_Grequest_complete(MPI_Request);
int MPI_Grequest_start(MPI_Grequest_query_function*, MPI_Grequest_free_function*, MPI_Grequest_cancel_function*, void*, MPI_Request*);
int MPI_Init_thread(int*, char***, int, int*);
int MPI_Is_thread_main(int*);
int MPI_Query_thread(int*);
int MPI_Status_set_cancelled(MPI_Status*, int);
int MPI_Status_set_elements(MPI_Status*, MPI_Datatype, int);
int MPI_Type_create_keyval(MPI_Type_copy_attr_function*, MPI_Type_delete_attr_function*, int*, void*);
int MPI_Type_delete_attr(MPI_Datatype, int);
int MPI_Type_dup(MPI_Datatype, MPI_Datatype*);
int MPI_Type_free_keyval(int*);
int MPI_Type_get_attr(MPI_Datatype, int, void*, int*);
int MPI_Type_get_contents(MPI_Datatype, int, int, int, int [], MPI_Aint [], MPI_Datatype []);
int MPI_Type_get_envelope(MPI_Datatype, int*, int*, int*, int*);
int MPI_Type_get_name(MPI_Datatype, char*, int*);
int MPI_Type_set_attr(MPI_Datatype, int, void*);
int MPI_Type_set_name(MPI_Datatype, char*);
int MPI_Type_match_size(int, int, MPI_Datatype*);
int MPI_Win_call_errhandler(MPI_Win, int);
int MPI_Win_create_keyval(MPI_Win_copy_attr_function*, MPI_Win_delete_attr_function*, int*, void*);
int MPI_Win_delete_attr(MPI_Win, int);
int MPI_Win_free_keyval(int*);
int MPI_Win_get_attr(MPI_Win, int, void*, int*);
int MPI_Win_get_name(MPI_Win, char*, int*);
int MPI_Win_set_attr(MPI_Win, int, void*);
int MPI_Win_set_name(MPI_Win, char*);
MPI_Comm MPI_Comm_f2c(MPI_Fint);
MPI_Datatype MPI_Type_f2c(MPI_Fint);
MPI_File MPI_File_f2c(MPI_Fint);
MPI_Fint MPI_Comm_c2f(MPI_Comm);
MPI_Fint MPI_File_c2f(MPI_File);
MPI_Fint MPI_Group_c2f(MPI_Group);
MPI_Fint MPI_Info_c2f(MPI_Info);
MPI_Fint MPI_Op_c2f(MPI_Op);
MPI_Fint MPI_Request_c2f(MPI_Request);
MPI_Fint MPI_Type_c2f(MPI_Datatype);
MPI_Fint MPI_Win_c2f(MPI_Win);
MPI_Group MPI_Group_f2c(MPI_Fint);
MPI_Info MPI_Info_f2c(MPI_Fint);
MPI_Op MPI_Op_f2c(MPI_Fint);
MPI_Request MPI_Request_f2c(MPI_Fint);
MPI_Win MPI_Win_f2c(MPI_Fint);
int MPI_Alloc_mem(MPI_Aint, MPI_Info info, void* baseptr);
int MPI_Comm_create_errhandler(MPI_Comm_errhandler_function*, MPI_Errhandler*);
int MPI_Comm_get_errhandler(MPI_Comm, MPI_Errhandler*);
int MPI_Comm_set_errhandler(MPI_Comm, MPI_Errhandler);
int MPI_File_create_errhandler(MPI_File_errhandler_function*, MPI_Errhandler*);
int MPI_File_get_errhandler(MPI_File, MPI_Errhandler*);
int MPI_File_set_errhandler(MPI_File, MPI_Errhandler);
int MPI_Finalized(int*);
int MPI_Free_mem(void*);
int MPI_Get_address(void*, MPI_Aint*);
int MPI_Info_create(MPI_Info*);
int MPI_Info_delete(MPI_Info, char*);
int MPI_Info_dup(MPI_Info, MPI_Info*);
int MPI_Info_free(MPI_Info* info);
int MPI_Info_get(MPI_Info, char*, int, char*, int*);
int MPI_Info_get_nkeys(MPI_Info, int*);
int MPI_Info_get_nthkey(MPI_Info, int, char*);
int MPI_Info_get_valuelen(MPI_Info, char*, int*, int*);
int MPI_Info_set(MPI_Info, char*, char*);
int MPI_Pack_external(char*, void*, int, MPI_Datatype, void*, MPI_Aint, MPI_Aint*);
int MPI_Pack_external_size(char*, int, MPI_Datatype, MPI_Aint*);
int MPI_Request_get_status(MPI_Request, int*, MPI_Status*);
int MPI_Status_c2f(MPI_Status*, MPI_Fint*);
int MPI_Status_f2c(MPI_Fint*, MPI_Status*);
int MPI_Type_create_darray(int, int, int, int [], int [], int [], int [], int, MPI_Datatype, MPI_Datatype*);
int MPI_Type_create_hindexed(int, int [], MPI_Aint [], MPI_Datatype, MPI_Datatype*);
int MPI_Type_create_hvector(int, int, MPI_Aint, MPI_Datatype, MPI_Datatype*);
int MPI_Type_create_indexed_block(int, int, int [], MPI_Datatype, MPI_Datatype*);
int MPIX_Type_create_hindexed_block(int, int, MPI_Aint [], MPI_Datatype, MPI_Datatype*);
int MPI_Type_create_resized(MPI_Datatype, MPI_Aint, MPI_Aint, MPI_Datatype*);
int MPI_Type_create_struct(int, int [], MPI_Aint [], MPI_Datatype [], MPI_Datatype*);
int MPI_Type_create_subarray(int, int [], int [], int [], int, MPI_Datatype, MPI_Datatype*);
int MPI_Type_get_extent(MPI_Datatype, MPI_Aint*, MPI_Aint*);
int MPI_Type_get_true_extent(MPI_Datatype, MPI_Aint*, MPI_Aint*);
int MPI_Unpack_external(char*, void*, MPI_Aint, MPI_Aint*, void*, int, MPI_Datatype);
int MPI_Win_create_errhandler(MPI_Win_errhandler_function*, MPI_Errhandler*);
int MPI_Win_get_errhandler(MPI_Win, MPI_Errhandler*);
int MPI_Win_set_errhandler(MPI_Win, MPI_Errhandler);
int MPI_Type_create_f90_integer(int, MPI_Datatype*);
int MPI_Type_create_f90_real(int, int, MPI_Datatype*);
int MPI_Type_create_f90_complex(int, int, MPI_Datatype*);
int MPI_Reduce_local(void* inbuf, void* inoutbuf, int count, MPI_Datatype datatype, MPI_Op op);
int MPI_Op_commutative(MPI_Op op, int* commute);
int MPI_Reduce_scatter_block(void* sendbuf, void* recvbuf, int recvcount, MPI_Datatype datatype, MPI_Op op, MPI_Comm comm);
int MPI_Dist_graph_create_adjacent(MPI_Comm comm_old, int indegree, int [], int [], int outdegree, int [], int [], MPI_Info info, int reorder, MPI_Comm* comm_dist_graph);
int MPI_Dist_graph_create(MPI_Comm comm_old, int n, int [], int [], int [], int [], MPI_Info info, int reorder, MPI_Comm* comm_dist_graph);
int MPI_Dist_graph_neighbors_count(MPI_Comm comm, int* indegree, int* outdegree, int* weighted);
int MPI_Dist_graph_neighbors(MPI_Comm comm, int maxindegree, int [], int [], int maxoutdegree, int [], int []);
const extern int* MPI_UNWEIGHTED;
extern MPI_Fint* MPI_F_STATUS_IGNORE;
extern MPI_Fint* MPI_F_STATUSES_IGNORE;
const extern struct MPIR_T_pvar_handle* MPI_T_PVAR_ALL_HANDLES;
typedef enum MPIR_T_verbosity_t{
  MPI_T_VERBOSITY_INVALID=0,
  MPI_T_VERBOSITY_USER_BASIC=221,
  MPI_T_VERBOSITY_USER_DETAIL,
  MPI_T_VERBOSITY_USER_ALL,
  MPI_T_VERBOSITY_TUNER_BASIC,
  MPI_T_VERBOSITY_TUNER_DETAIL,
  MPI_T_VERBOSITY_TUNER_ALL,
  MPI_T_VERBOSITY_MPIDEV_BASIC,
  MPI_T_VERBOSITY_MPIDEV_DETAIL,
  MPI_T_VERBOSITY_MPIDEV_ALL
} MPIR_T_verbosity_t;
typedef enum MPIR_T_bind_t{
  MPI_T_BIND_INVALID=0,
  MPI_T_BIND_NO_OBJECT=9700,
  MPI_T_BIND_MPI_COMM,
  MPI_T_BIND_MPI_DATATYPE,
  MPI_T_BIND_MPI_ERRHANDLER,
  MPI_T_BIND_MPI_FILE,
  MPI_T_BIND_MPI_GROUP,
  MPI_T_BIND_MPI_OP,
  MPI_T_BIND_MPI_REQUEST,
  MPI_T_BIND_MPI_WIN,
  MPI_T_BIND_MPI_MESSAGE,
  MPI_T_BIND_MPI_INFO
} MPIR_T_bind_t;
typedef enum MPIR_T_scope_t{
  MPI_T_SCOPE_INVALID=0,
  MPI_T_SCOPE_READONLY=60439,
  MPI_T_SCOPE_LOCAL,
  MPI_T_SCOPE_GROUP,
  MPI_T_SCOPE_GROUP_EQ,
  MPI_T_SCOPE_ALL,
  MPI_T_SCOPE_ALL_EQ
} MPIR_T_scope_t;
typedef enum MPIR_T_pvar_class_t{
  MPI_T_PVAR_CLASS_INVALID=0,
  MPI_T_PVAR_CLASS_STATE=240,
  MPI_T_PVAR_CLASS_LEVEL,
  MPI_T_PVAR_CLASS_SIZE,
  MPI_T_PVAR_CLASS_PERCENTAGE,
  MPI_T_PVAR_CLASS_HIGHWATERMARK,
  MPI_T_PVAR_CLASS_LOWWATERMARK,
  MPI_T_PVAR_CLASS_COUNTER,
  MPI_T_PVAR_CLASS_AGGREGATE,
  MPI_T_PVAR_CLASS_TIMER,
  MPI_T_PVAR_CLASS_GENERIC
} MPIR_T_pvar_class_t;
//======================== civlc.cvh =======================
typedef unsigned long size_t;
typedef struct $proc $proc;
typedef struct $scope $scope;
typedef struct $dynamic $dynamic;
typedef enum Operation $operation;
$system[civlc] void $wait($proc p);
$system[civlc] void $waitall($proc* procs, int numProcs);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $exit(void);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] int $choose_int(int n);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $assert(_Bool expr, ...);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $assume(_Bool expr);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $elaborate(int x);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] int $next_time_count(void);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $pathCondition(void);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] _Bool $is_concrete_int(int value);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void* $malloc($scope s, int size);
/*@ depends_on \write(p);
  @ executes_when $true;
  @*/
$system[civlc] void $free(void* p);
/*@ depends_on \write(ptr);
  @ executes_when $true;
  @*/
$system[civlc] void $havoc(void* ptr);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] double $pow(double base, double exp);
//======================= bundle.cvh =======================
typedef struct _bundle $bundle;
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[bundle] int $bundle_size($bundle b);
/*@ depends_on \write(ptr);
  @ executes_when $true;
  @*/
$system[bundle] $bundle $bundle_pack(void* ptr, int size);
/*@ depends_on \write(ptr);
  @ executes_when $true;
  @*/
$system[bundle] void $bundle_unpack($bundle bundle, void* ptr);
/*@ depends_on \write(buf);
  @ executes_when $true;
  @*/
$system[bundle] void $bundle_unpack_apply($bundle data, void* buf, int size, $operation op);
//======================== comm.cvh ========================
typedef struct _message{
    int source;
    int dest;
    int tag;
    $bundle data;
    int size;
} $message;
typedef struct _queue $queue;
typedef struct _gcomm* $gcomm;
typedef struct _comm* $comm;
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f $message $message_pack(int source, int dest, int tag, void* data, int size);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f int $message_source($message message);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f int $message_tag($message message);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f int $message_dest($message message);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f int $message_size($message message);
/*@ depends_on \write(buf);
  @ executes_when $true;
  @*/
$atomic_f void $message_unpack($message message, void* buf, int size);
/*@ depends_on \nothing;
  @ assigns \nothing;
  @ reads \nothing;
  @*/
$atomic_f $gcomm $gcomm_create($scope scope, int size);
/*@ depends_on \write(junkMsgs), \write(gcomm);
  @ assigns junkMsgs, gcomm;
  @*/
$atomic_f int $gcomm_destroy($gcomm gcomm, void* junkMsgs);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[comm] void $gcomm_dup($comm comm, $comm newcomm);
$atomic_f $comm $comm_create($scope scope, $gcomm gcomm, int place);
/*@ depends_on \write(comm);
  @ assigns comm;
  @ reads \nothing;
  @*/
$atomic_f void $comm_destroy($comm comm);
/*@ pure;
  @ depends_on \nothing;
  @*/
$atomic_f int $comm_size($comm comm);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f int $comm_place($comm comm);
/*@ depends_on \write(comm);
  @ executes_when $true;
  @*/
$system[comm] void $comm_enqueue($comm comm, $message message);
/*@ pure;
  @ depends_on \write(comm);
  @ executes_when $true;
  @*/
$system[comm] _Bool $comm_probe($comm comm, int source, int tag);
/*@ pure;
  @ depends_on \write(comm);
  @ executes_when $true;
  @*/
$system[comm] $message $comm_seek($comm comm, int source, int tag);
/*@ depends_on \write(comm);
  @ executes_when $comm_probe(comm, source, tag);
  @*/
$system[comm] $message $comm_dequeue($comm comm, int source, int tag);
//===================== concurrency.cvh ====================
typedef struct _gbarrier* $gbarrier;
typedef struct _barrier* $barrier;
/*@ depends_on \nothing;
  @ assigns \nothing;
  @ reads \nothing;
  @*/
$atomic_f $gbarrier $gbarrier_create($scope scope, int size);
/*@ depends_on \write(gbarrier);
  @ reads \nothing;
  @ assigns gbarrier;
  @*/
$atomic_f void $gbarrier_destroy($gbarrier gbarrier);
/*@ depends_on \nothing;
  @ assigns gbarrier;
  @ reads gbarrier;
  @*/
$atomic_f $barrier $barrier_create($scope scope, $gbarrier gbarrier, int place);
/*@ depends_on \write(barrier);
  @ assigns barrier;
  @ reads \nothing;
  @*/
$atomic_f void $barrier_destroy($barrier barrier);
void $barrier_call($barrier barrier);
typedef struct _collator_entry $collator_entry;
typedef struct _gcollator* $gcollator;
typedef struct _collator* $collator;
/*@ depends_on \nothing;
  @ reads \nothing;
  @ assigns \nothing;
  @*/
$atomic_f $gcollator $gcollator_create($scope scope);
/*@ depends_on \write(gcollator);
  @ assigns gcollator;
  @ reads \nothing;
  @*/
$atomic_f int $gcollator_destroy($gcollator gcollator);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f $collator $collator_create($scope scope, $gcollator gcollator);
/*@ depends_on \write(collator);
  @ executes_when $true;
  @*/
$atomic_f void $collator_destroy($collator collator);
/*@ depends_on \write(collator);
  @ executes_when $true;
  @*/
$system[concurrency] $bundle $collator_check($collator collator, int place, int nprocs, $bundle entries);
//======================= collate.cvh ======================
typedef struct _gcollator* $gcollator;
typedef struct _collator* $collator;
typedef struct _gcollate_state* $gcollate_state;
typedef struct _collate_state* $collate_state;
$gcollator gcollator_create($scope scope, int nprocs);
$collator collator_create($gcollator gcollator, int place);
$collate_state $collate_snapshot($collator c);
$collate_state $collate_unsnapshot($collator c);
/*@ pure;
  @*/
$system[collate] _Bool $collate_arrived($collate_state cp, $range r);
/*@ pure;
  @*/
$system[collate] _Bool $collate_complete($collate_state cp);
//====================== civl-mpi.cvh ======================
typedef enum _mpi_state{
  _MPI_UNINIT,
  _MPI_INIT,
  _MPI_FINALIZED
} $mpi_state;
typedef struct MPI_Comm MPI_Comm;
typedef struct MPI_Status MPI_Status;
typedef struct $mpi_gcomm $mpi_gcomm;
int sizeofDatatype(MPI_Datatype);
$abstract double $mpi_time(int i);
$mpi_gcomm $mpi_gcomm_create($scope, int);
void $mpi_gcomm_destroy($mpi_gcomm);
MPI_Comm $mpi_comm_create($scope, $mpi_gcomm, int);
void $mpi_comm_destroy(MPI_Comm, $mpi_state);
int $mpi_send(void*, int, MPI_Datatype, int, int, MPI_Comm);
int $mpi_recv(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Status*);
int $mpi_sendrecv(void* sendbuf, int sendcount, MPI_Datatype sendtype, int dest, int sendtag, void* recvbuf, int recvcount, MPI_Datatype recvtype, int source, int recvtag, MPI_Comm comm, MPI_Status* status);
int $mpi_collective_send(void*, int, MPI_Datatype, int, int, MPI_Comm);
int $mpi_collective_recv(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Status*, char*);
int $mpi_bcast(void*, int, MPI_Datatype, int, int, MPI_Comm, char*);
int $mpi_reduce(void*, void*, int, MPI_Datatype, MPI_Op, int, int, MPI_Comm, char*);
int $mpi_gather(void*, int, MPI_Datatype, void*, int, MPI_Datatype, int, int, MPI_Comm, char*);
int $mpi_gatherv(void*, int, MPI_Datatype, void*, int [], int [], MPI_Datatype, int, int, MPI_Comm, char*);
int $mpi_scatter(void*, int, MPI_Datatype, void*, int, MPI_Datatype, int, int, MPI_Comm, char*);
int $mpi_scatterv(void*, int [], int [], MPI_Datatype, void*, int, MPI_Datatype, int, int, MPI_Comm, char*);
void* $mpi_pointer_add(void*, int, MPI_Datatype);
$system[mpi] int $mpi_new_gcomm($scope, $mpi_gcomm);
$system[mpi] $mpi_gcomm $mpi_get_gcomm($scope, int);
int $mpi_comm_dup($scope, MPI_Comm, MPI_Comm*, char*);
int $mpi_comm_free(MPI_Comm*, $mpi_state);
$system[mpi] $scope $mpi_root_scope($comm);
$system[mpi] $scope $mpi_proc_scope($comm);
$system[mpi] void $mpi_check_buffer(void* buf, int count, MPI_Datatype datatype);
$bundle $mpi_create_coroutine_entry(int routineTag, int root, int op, int numDatatypes, int* datatypes);
void $mpi_diff_coroutine_entries($bundle specEntry, $bundle mineEntry, int rank);
void $mpi_coassert(MPI_Comm, _Bool);
_Bool $mpi_isRecvBufEmpty(int x);
/*@ depends_on \nothing;
  @*/
$system[mpi] void $mpi_p2pSendShot(int commID, $message msg, int place);
/*@ depends_on \nothing;
  @*/
$system[mpi] void $mpi_colSendShot(int commID, $message msg, int place);
/*@ depends_on \nothing;
  @*/
$system[mpi] void $mpi_p2pRecvShot(int commID, int source, int dest, int tag);
/*@ depends_on \nothing;
  @*/
$system[mpi] void $mpi_colRecvShot(int commID, int source, int dest, int tag);
//======================== stddef.h ========================
typedef long ptrdiff_t;
typedef unsigned long size_t;
typedef struct max_align_t max_align_t;
typedef long wchar_t;
//======================== string.h ========================
void* memcpy(void* p, void* q, size_t size);
void* memmove(void* dest, void* src, size_t n);
$system[string] void* memset(void* s, int c, size_t n);
int memcmp(void* s1, void* s2, size_t n);
void* memchr(void* s, int c, size_t n);
$system[string] char* strcpy(char* restrict s1, char* restrict s2);
char* strncpy(char* dest, char* src, size_t n);
char* strcat(char* dest, char* src);
char* strncat(char* dest, char* src, size_t n);
$system[string] int strcmp(char* s1, char* s2);
int strncmp(char* s1, char* s2, size_t n);
int strcoll(char* s1, char* s2);
size_t strxfrm(char* dest, char* src, size_t n);
char* strchr(char* s, int c);
char* strrchr(char* s, int c);
size_t strcspn(char* s, char* reject);
size_t strspn(char* s, char* accept);
char* strpbrk(char* s, char* accept);
char* strstr(char* s1, char* s2);
char* strtok(char* s, char* delim);
$system[string] size_t strlen(char* s);
char* strerror(int errnum);
//======================== civlc.cvh =======================
$system[civlc] void $wait($proc p);
$system[civlc] void $waitall($proc* procs, int numProcs);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $exit(void);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] int $choose_int(int n);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $assert(_Bool expr, ...);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $assume(_Bool expr);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $elaborate(int x);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] int $next_time_count(void);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $pathCondition(void);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] _Bool $is_concrete_int(int value);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void* $malloc($scope s, int size);
/*@ depends_on \write(p);
  @ executes_when $true;
  @*/
$system[civlc] void $free(void* p);
/*@ depends_on \write(ptr);
  @ executes_when $true;
  @*/
$system[civlc] void $havoc(void* ptr);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] double $pow(double base, double exp);
//======================= bundle.cvh =======================
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[bundle] int $bundle_size($bundle b);
/*@ depends_on \write(ptr);
  @ executes_when $true;
  @*/
$system[bundle] $bundle $bundle_pack(void* ptr, int size);
/*@ depends_on \write(ptr);
  @ executes_when $true;
  @*/
$system[bundle] void $bundle_unpack($bundle bundle, void* ptr);
/*@ depends_on \write(buf);
  @ executes_when $true;
  @*/
$system[bundle] void $bundle_unpack_apply($bundle data, void* buf, int size, $operation op);
//===================== concurrency.cvh ====================
/*@ depends_on \nothing;
  @ assigns \nothing;
  @ reads \nothing;
  @*/
$atomic_f $gbarrier $gbarrier_create($scope scope, int size);
/*@ depends_on \write(gbarrier);
  @ reads \nothing;
  @ assigns gbarrier;
  @*/
$atomic_f void $gbarrier_destroy($gbarrier gbarrier);
/*@ depends_on \nothing;
  @ assigns gbarrier;
  @ reads gbarrier;
  @*/
$atomic_f $barrier $barrier_create($scope scope, $gbarrier gbarrier, int place);
/*@ depends_on \write(barrier);
  @ assigns barrier;
  @ reads \nothing;
  @*/
$atomic_f void $barrier_destroy($barrier barrier);
void $barrier_call($barrier barrier);
/*@ depends_on \nothing;
  @ reads \nothing;
  @ assigns \nothing;
  @*/
$atomic_f $gcollator $gcollator_create($scope scope);
/*@ depends_on \write(gcollator);
  @ assigns gcollator;
  @ reads \nothing;
  @*/
$atomic_f int $gcollator_destroy($gcollator gcollator);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f $collator $collator_create($scope scope, $gcollator gcollator);
/*@ depends_on \write(collator);
  @ executes_when $true;
  @*/
$atomic_f void $collator_destroy($collator collator);
/*@ depends_on \write(collator);
  @ executes_when $true;
  @*/
$system[concurrency] $bundle $collator_check($collator collator, int place, int nprocs, $bundle entries);
//========================== mpi.h =========================
MPI_Comm MPI_COMM_WORLD;
MPI_Comm MPI_COMM_SELF;
MPI_Comm MPI_COMM_PARENT;
MPI_Comm MPI_COMM_TYPE_SHARED;
int MPI_Send(void*, int, MPI_Datatype, int, int, MPI_Comm);
int MPI_Recv(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Status*);
int MPI_Get_count(MPI_Status*, MPI_Datatype, int*);
int MPI_Bsend(void*, int, MPI_Datatype, int, int, MPI_Comm);
int MPI_Ssend(void*, int, MPI_Datatype, int, int, MPI_Comm);
int MPI_Rsend(void*, int, MPI_Datatype, int, int, MPI_Comm);
int MPI_Buffer_attach(void*, int);
int MPI_Buffer_detach(void*, int*);
int MPI_Isend(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Ibsend(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Issend(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Irsend(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Irecv(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Wait(MPI_Request*, MPI_Status*);
int MPI_Test(MPI_Request*, int*, MPI_Status*);
int MPI_Request_free(MPI_Request*);
int MPI_Waitany(int, MPI_Request*, int*, MPI_Status*);
int MPI_Testany(int, MPI_Request*, int*, int*, MPI_Status*);
int MPI_Waitall(int, MPI_Request*, MPI_Status*);
int MPI_Testall(int, MPI_Request*, int*, MPI_Status*);
int MPI_Waitsome(int, MPI_Request*, int*, int*, MPI_Status*);
int MPI_Testsome(int, MPI_Request*, int*, int*, MPI_Status*);
int MPI_Iprobe(int, int, MPI_Comm, int*, MPI_Status*);
int MPI_Probe(int, int, MPI_Comm, MPI_Status*);
int MPI_Cancel(MPI_Request*);
int MPI_Test_cancelled(MPI_Status*, int*);
int MPI_Send_init(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Bsend_init(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Ssend_init(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Rsend_init(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Recv_init(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Start(MPI_Request*);
int MPI_Startall(int, MPI_Request*);
int MPI_Sendrecv(void*, int, MPI_Datatype, int, int, void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Status*);
int MPI_Sendrecv_replace(void*, int, MPI_Datatype, int, int, int, int, MPI_Comm, MPI_Status*);
int MPI_Type_contiguous(int, MPI_Datatype, MPI_Datatype*);
int MPI_Type_vector(int, int, int, MPI_Datatype, MPI_Datatype*);
int MPI_Type_hvector(int, int, MPI_Aint, MPI_Datatype, MPI_Datatype*);
int MPI_Type_indexed(int, int*, int*, MPI_Datatype, MPI_Datatype*);
int MPI_Type_hindexed(int, int*, MPI_Aint*, MPI_Datatype, MPI_Datatype*);
int MPI_Type_struct(int, int*, MPI_Aint*, MPI_Datatype*, MPI_Datatype*);
int MPI_Address(void*, MPI_Aint*);
int MPI_Type_extent(MPI_Datatype, MPI_Aint*);
int MPI_Type_size(MPI_Datatype, int*);
int MPI_Type_lb(MPI_Datatype, MPI_Aint*);
int MPI_Type_ub(MPI_Datatype, MPI_Aint*);
int MPI_Type_commit(MPI_Datatype*);
int MPI_Type_free(MPI_Datatype*);
int MPI_Get_elements(MPI_Status*, MPI_Datatype, int*);
int MPI_Pack(void*, int, MPI_Datatype, void*, int, int*, MPI_Comm);
int MPI_Unpack(void*, int, int*, void*, int, MPI_Datatype, MPI_Comm);
int MPI_Pack_size(int, MPI_Datatype, MPI_Comm, int*);
int MPI_Barrier(MPI_Comm);
int MPI_Bcast(void*, int, MPI_Datatype, int, MPI_Comm);
int MPI_Gather(void*, int, MPI_Datatype, void*, int, MPI_Datatype, int, MPI_Comm);
int MPI_Gatherv(void*, int, MPI_Datatype, void*, int*, int*, MPI_Datatype, int, MPI_Comm);
int MPI_Scatter(void*, int, MPI_Datatype, void*, int, MPI_Datatype, int, MPI_Comm);
int MPI_Scatterv(void*, int*, int*, MPI_Datatype, void*, int, MPI_Datatype, int, MPI_Comm);
int MPI_Allgather(void*, int, MPI_Datatype, void*, int, MPI_Datatype, MPI_Comm);
int MPI_Allgatherv(void*, int, MPI_Datatype, void*, int*, int*, MPI_Datatype, MPI_Comm);
int MPI_Alltoall(void*, int, MPI_Datatype, void*, int, MPI_Datatype, MPI_Comm);
int MPI_Alltoallv(void*, int*, int*, MPI_Datatype, void*, int*, int*, MPI_Datatype, MPI_Comm);
int MPI_Reduce(void*, void*, int, MPI_Datatype, MPI_Op, int, MPI_Comm);
int MPI_Op_create(MPI_User_function*, int, MPI_Op*);
int MPI_Op_free(MPI_Op*);
int MPI_Allreduce(void*, void*, int, MPI_Datatype, MPI_Op, MPI_Comm);
int MPI_Reduce_scatter(void*, void*, int*, MPI_Datatype, MPI_Op, MPI_Comm);
int MPI_Scan(void*, void*, int, MPI_Datatype, MPI_Op, MPI_Comm);
int MPI_Group_size(MPI_Group, int*);
int MPI_Group_rank(MPI_Group, int*);
int MPI_Group_translate_ranks(MPI_Group, int, int*, MPI_Group, int*);
int MPI_Group_compare(MPI_Group, MPI_Group, int*);
int MPI_Comm_group(MPI_Comm, MPI_Group*);
int MPI_Group_union(MPI_Group, MPI_Group, MPI_Group*);
int MPI_Group_intersection(MPI_Group, MPI_Group, MPI_Group*);
int MPI_Group_difference(MPI_Group, MPI_Group, MPI_Group*);
int MPI_Group_incl(MPI_Group, int, int*, MPI_Group*);
int MPI_Group_excl(MPI_Group, int, int*, MPI_Group*);
int MPI_Group_range_incl(MPI_Group, int, int [][3], MPI_Group*);
int MPI_Group_range_excl(MPI_Group, int, int [][3], MPI_Group*);
int MPI_Group_free(MPI_Group*);
int MPI_Comm_size(MPI_Comm, int*);
int MPI_Comm_rank(MPI_Comm, int*);
int MPI_Comm_compare(MPI_Comm, MPI_Comm, int*);
int MPI_Comm_dup(MPI_Comm, MPI_Comm*);
int MPI_Comm_create(MPI_Comm, MPI_Group, MPI_Comm*);
int MPI_Comm_split(MPI_Comm, int, int, MPI_Comm*);
int MPI_Comm_free(MPI_Comm*);
int MPI_Comm_test_inter(MPI_Comm, int*);
int MPI_Comm_remote_size(MPI_Comm, int*);
int MPI_Comm_remote_group(MPI_Comm, MPI_Group*);
int MPI_Intercomm_create(MPI_Comm, int, MPI_Comm, int, int, MPI_Comm*);
int MPI_Intercomm_merge(MPI_Comm, int, MPI_Comm*);
int MPI_Keyval_create(MPI_Copy_function*, MPI_Delete_function*, int*, void*);
int MPI_Keyval_free(int*);
int MPI_Attr_put(MPI_Comm, int, void*);
int MPI_Attr_get(MPI_Comm, int, void*, int*);
int MPI_Attr_delete(MPI_Comm, int);
int MPI_Topo_test(MPI_Comm, int*);
int MPI_Cart_create(MPI_Comm, int, int*, int*, int, MPI_Comm*);
int MPI_Dims_create(int, int, int*);
int MPI_Graph_create(MPI_Comm, int, int*, int*, int, MPI_Comm*);
int MPI_Graphdims_get(MPI_Comm, int*, int*);
int MPI_Graph_get(MPI_Comm, int, int, int*, int*);
int MPI_Cartdim_get(MPI_Comm, int*);
int MPI_Cart_get(MPI_Comm, int, int*, int*, int*);
int MPI_Cart_rank(MPI_Comm, int*, int*);
int MPI_Cart_coords(MPI_Comm, int, int, int*);
int MPI_Graph_neighbors_count(MPI_Comm, int, int*);
int MPI_Graph_neighbors(MPI_Comm, int, int, int*);
int MPI_Cart_shift(MPI_Comm, int, int, int*, int*);
int MPI_Cart_sub(MPI_Comm, int*, MPI_Comm*);
int MPI_Cart_map(MPI_Comm, int, int*, int*, int*);
int MPI_Graph_map(MPI_Comm, int, int*, int*, int*);
int MPI_Get_processor_name(char*, int*);
int MPI_Get_version(int*, int*);
int MPI_Errhandler_create(MPI_Handler_function*, MPI_Errhandler*);
int MPI_Errhandler_set(MPI_Comm, MPI_Errhandler);
int MPI_Errhandler_get(MPI_Comm, MPI_Errhandler*);
int MPI_Errhandler_free(MPI_Errhandler*);
int MPI_Error_string(int, char*, int*);
int MPI_Error_class(int, int*);
double MPI_Wtime(void);
double MPI_Wtick(void);
int MPI_Init(int*, char***);
int MPI_Finalize(void);
int MPI_Initialized(int*);
$system[mpi] int MPI_Abort(MPI_Comm, int);
int MPI_Pcontrol(const int, ...);
int MPI_DUP_FN(MPI_Comm, int, void*, void*, void*, int*);
int MPI_Close_port(char*);
int MPI_Comm_accept(char*, MPI_Info, int, MPI_Comm, MPI_Comm*);
int MPI_Comm_connect(char*, MPI_Info, int, MPI_Comm, MPI_Comm*);
int MPI_Comm_disconnect(MPI_Comm*);
int MPI_Comm_get_parent(MPI_Comm*);
int MPI_Comm_join(int, MPI_Comm*);
int MPI_Comm_spawn(char*, char* [], int, MPI_Info, int, MPI_Comm, MPI_Comm*, int []);
int MPI_Comm_spawn_multiple(int, char* [], char** [], int [], MPI_Info [], int, MPI_Comm, MPI_Comm*, int []);
int MPI_Lookup_name(char*, MPI_Info, char*);
int MPI_Open_port(MPI_Info, char*);
int MPI_Publish_name(char*, MPI_Info, char*);
int MPI_Unpublish_name(char*, MPI_Info, char*);
int MPI_Accumulate(void*, int, MPI_Datatype, int, MPI_Aint, int, MPI_Datatype, MPI_Op, MPI_Win);
int MPI_Get(void*, int, MPI_Datatype, int, MPI_Aint, int, MPI_Datatype, MPI_Win);
int MPI_Put(void*, int, MPI_Datatype, int, MPI_Aint, int, MPI_Datatype, MPI_Win);
int MPI_Win_complete(MPI_Win);
int MPI_Win_create(void*, MPI_Aint, int, MPI_Info, MPI_Comm, MPI_Win*);
int MPI_Win_fence(int, MPI_Win);
int MPI_Win_free(MPI_Win*);
int MPI_Win_get_group(MPI_Win, MPI_Group*);
int MPI_Win_lock(int, int, int, MPI_Win);
int MPI_Win_post(MPI_Group, int, MPI_Win);
int MPI_Win_start(MPI_Group, int, MPI_Win);
int MPI_Win_test(MPI_Win, int*);
int MPI_Win_unlock(int, MPI_Win);
int MPI_Win_wait(MPI_Win);
int MPI_Alltoallw(void*, int [], int [], MPI_Datatype [], void*, int [], int [], MPI_Datatype [], MPI_Comm);
int MPI_Exscan(void*, void*, int, MPI_Datatype, MPI_Op, MPI_Comm);
int MPI_Add_error_class(int*);
int MPI_Add_error_code(int, int*);
int MPI_Add_error_string(int, char*);
int MPI_Comm_call_errhandler(MPI_Comm, int);
int MPI_Comm_create_keyval(MPI_Comm_copy_attr_function*, MPI_Comm_delete_attr_function*, int*, void*);
int MPI_Comm_delete_attr(MPI_Comm, int);
int MPI_Comm_free_keyval(int*);
int MPI_Comm_get_attr(MPI_Comm, int, void*, int*);
int MPI_Comm_get_name(MPI_Comm, char*, int*);
int MPI_Comm_set_attr(MPI_Comm, int, void*);
int MPI_Comm_set_name(MPI_Comm, char*);
int MPI_File_call_errhandler(MPI_File, int);
int MPI_Grequest_complete(MPI_Request);
int MPI_Grequest_start(MPI_Grequest_query_function*, MPI_Grequest_free_function*, MPI_Grequest_cancel_function*, void*, MPI_Request*);
int MPI_Init_thread(int*, char***, int, int*);
int MPI_Is_thread_main(int*);
int MPI_Query_thread(int*);
int MPI_Status_set_cancelled(MPI_Status*, int);
int MPI_Status_set_elements(MPI_Status*, MPI_Datatype, int);
int MPI_Type_create_keyval(MPI_Type_copy_attr_function*, MPI_Type_delete_attr_function*, int*, void*);
int MPI_Type_delete_attr(MPI_Datatype, int);
int MPI_Type_dup(MPI_Datatype, MPI_Datatype*);
int MPI_Type_free_keyval(int*);
int MPI_Type_get_attr(MPI_Datatype, int, void*, int*);
int MPI_Type_get_contents(MPI_Datatype, int, int, int, int [], MPI_Aint [], MPI_Datatype []);
int MPI_Type_get_envelope(MPI_Datatype, int*, int*, int*, int*);
int MPI_Type_get_name(MPI_Datatype, char*, int*);
int MPI_Type_set_attr(MPI_Datatype, int, void*);
int MPI_Type_set_name(MPI_Datatype, char*);
int MPI_Type_match_size(int, int, MPI_Datatype*);
int MPI_Win_call_errhandler(MPI_Win, int);
int MPI_Win_create_keyval(MPI_Win_copy_attr_function*, MPI_Win_delete_attr_function*, int*, void*);
int MPI_Win_delete_attr(MPI_Win, int);
int MPI_Win_free_keyval(int*);
int MPI_Win_get_attr(MPI_Win, int, void*, int*);
int MPI_Win_get_name(MPI_Win, char*, int*);
int MPI_Win_set_attr(MPI_Win, int, void*);
int MPI_Win_set_name(MPI_Win, char*);
MPI_Comm MPI_Comm_f2c(MPI_Fint);
MPI_Datatype MPI_Type_f2c(MPI_Fint);
MPI_File MPI_File_f2c(MPI_Fint);
MPI_Fint MPI_Comm_c2f(MPI_Comm);
MPI_Fint MPI_File_c2f(MPI_File);
MPI_Fint MPI_Group_c2f(MPI_Group);
MPI_Fint MPI_Info_c2f(MPI_Info);
MPI_Fint MPI_Op_c2f(MPI_Op);
MPI_Fint MPI_Request_c2f(MPI_Request);
MPI_Fint MPI_Type_c2f(MPI_Datatype);
MPI_Fint MPI_Win_c2f(MPI_Win);
MPI_Group MPI_Group_f2c(MPI_Fint);
MPI_Info MPI_Info_f2c(MPI_Fint);
MPI_Op MPI_Op_f2c(MPI_Fint);
MPI_Request MPI_Request_f2c(MPI_Fint);
MPI_Win MPI_Win_f2c(MPI_Fint);
int MPI_Alloc_mem(MPI_Aint, MPI_Info info, void* baseptr);
int MPI_Comm_create_errhandler(MPI_Comm_errhandler_function*, MPI_Errhandler*);
int MPI_Comm_get_errhandler(MPI_Comm, MPI_Errhandler*);
int MPI_Comm_set_errhandler(MPI_Comm, MPI_Errhandler);
int MPI_File_create_errhandler(MPI_File_errhandler_function*, MPI_Errhandler*);
int MPI_File_get_errhandler(MPI_File, MPI_Errhandler*);
int MPI_File_set_errhandler(MPI_File, MPI_Errhandler);
int MPI_Finalized(int*);
int MPI_Free_mem(void*);
int MPI_Get_address(void*, MPI_Aint*);
int MPI_Info_create(MPI_Info*);
int MPI_Info_delete(MPI_Info, char*);
int MPI_Info_dup(MPI_Info, MPI_Info*);
int MPI_Info_free(MPI_Info* info);
int MPI_Info_get(MPI_Info, char*, int, char*, int*);
int MPI_Info_get_nkeys(MPI_Info, int*);
int MPI_Info_get_nthkey(MPI_Info, int, char*);
int MPI_Info_get_valuelen(MPI_Info, char*, int*, int*);
int MPI_Info_set(MPI_Info, char*, char*);
int MPI_Pack_external(char*, void*, int, MPI_Datatype, void*, MPI_Aint, MPI_Aint*);
int MPI_Pack_external_size(char*, int, MPI_Datatype, MPI_Aint*);
int MPI_Request_get_status(MPI_Request, int*, MPI_Status*);
int MPI_Status_c2f(MPI_Status*, MPI_Fint*);
int MPI_Status_f2c(MPI_Fint*, MPI_Status*);
int MPI_Type_create_darray(int, int, int, int [], int [], int [], int [], int, MPI_Datatype, MPI_Datatype*);
int MPI_Type_create_hindexed(int, int [], MPI_Aint [], MPI_Datatype, MPI_Datatype*);
int MPI_Type_create_hvector(int, int, MPI_Aint, MPI_Datatype, MPI_Datatype*);
int MPI_Type_create_indexed_block(int, int, int [], MPI_Datatype, MPI_Datatype*);
int MPIX_Type_create_hindexed_block(int, int, MPI_Aint [], MPI_Datatype, MPI_Datatype*);
int MPI_Type_create_resized(MPI_Datatype, MPI_Aint, MPI_Aint, MPI_Datatype*);
int MPI_Type_create_struct(int, int [], MPI_Aint [], MPI_Datatype [], MPI_Datatype*);
int MPI_Type_create_subarray(int, int [], int [], int [], int, MPI_Datatype, MPI_Datatype*);
int MPI_Type_get_extent(MPI_Datatype, MPI_Aint*, MPI_Aint*);
int MPI_Type_get_true_extent(MPI_Datatype, MPI_Aint*, MPI_Aint*);
int MPI_Unpack_external(char*, void*, MPI_Aint, MPI_Aint*, void*, int, MPI_Datatype);
int MPI_Win_create_errhandler(MPI_Win_errhandler_function*, MPI_Errhandler*);
int MPI_Win_get_errhandler(MPI_Win, MPI_Errhandler*);
int MPI_Win_set_errhandler(MPI_Win, MPI_Errhandler);
int MPI_Type_create_f90_integer(int, MPI_Datatype*);
int MPI_Type_create_f90_real(int, int, MPI_Datatype*);
int MPI_Type_create_f90_complex(int, int, MPI_Datatype*);
int MPI_Reduce_local(void* inbuf, void* inoutbuf, int count, MPI_Datatype datatype, MPI_Op op);
int MPI_Op_commutative(MPI_Op op, int* commute);
int MPI_Reduce_scatter_block(void* sendbuf, void* recvbuf, int recvcount, MPI_Datatype datatype, MPI_Op op, MPI_Comm comm);
int MPI_Dist_graph_create_adjacent(MPI_Comm comm_old, int indegree, int [], int [], int outdegree, int [], int [], MPI_Info info, int reorder, MPI_Comm* comm_dist_graph);
int MPI_Dist_graph_create(MPI_Comm comm_old, int n, int [], int [], int [], int [], MPI_Info info, int reorder, MPI_Comm* comm_dist_graph);
int MPI_Dist_graph_neighbors_count(MPI_Comm comm, int* indegree, int* outdegree, int* weighted);
int MPI_Dist_graph_neighbors(MPI_Comm comm, int maxindegree, int [], int [], int maxoutdegree, int [], int []);
const extern int* MPI_UNWEIGHTED;
extern MPI_Fint* MPI_F_STATUS_IGNORE;
extern MPI_Fint* MPI_F_STATUSES_IGNORE;
const extern struct MPIR_T_pvar_handle* MPI_T_PVAR_ALL_HANDLES;
//======================== comm.cvh ========================
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f $message $message_pack(int source, int dest, int tag, void* data, int size);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f int $message_source($message message);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f int $message_tag($message message);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f int $message_dest($message message);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f int $message_size($message message);
/*@ depends_on \write(buf);
  @ executes_when $true;
  @*/
$atomic_f void $message_unpack($message message, void* buf, int size);
/*@ depends_on \nothing;
  @ assigns \nothing;
  @ reads \nothing;
  @*/
$atomic_f $gcomm $gcomm_create($scope scope, int size);
/*@ depends_on \write(junkMsgs), \write(gcomm);
  @ assigns junkMsgs, gcomm;
  @*/
$atomic_f int $gcomm_destroy($gcomm gcomm, void* junkMsgs);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[comm] void $gcomm_dup($comm comm, $comm newcomm);
$atomic_f $comm $comm_create($scope scope, $gcomm gcomm, int place);
/*@ depends_on \write(comm);
  @ assigns comm;
  @ reads \nothing;
  @*/
$atomic_f void $comm_destroy($comm comm);
/*@ pure;
  @ depends_on \nothing;
  @*/
$atomic_f int $comm_size($comm comm);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f int $comm_place($comm comm);
/*@ depends_on \write(comm);
  @ executes_when $true;
  @*/
$system[comm] void $comm_enqueue($comm comm, $message message);
/*@ pure;
  @ depends_on \write(comm);
  @ executes_when $true;
  @*/
$system[comm] _Bool $comm_probe($comm comm, int source, int tag);
/*@ pure;
  @ depends_on \write(comm);
  @ executes_when $true;
  @*/
$system[comm] $message $comm_seek($comm comm, int source, int tag);
/*@ depends_on \write(comm);
  @ executes_when $comm_probe(comm, source, tag);
  @*/
$system[comm] $message $comm_dequeue($comm comm, int source, int tag);
//====================== civl-mpi.cvh ======================
int sizeofDatatype(MPI_Datatype);
$abstract double $mpi_time(int i);
$mpi_gcomm $mpi_gcomm_create($scope, int);
void $mpi_gcomm_destroy($mpi_gcomm);
MPI_Comm $mpi_comm_create($scope, $mpi_gcomm, int);
void $mpi_comm_destroy(MPI_Comm, $mpi_state);
int $mpi_send(void*, int, MPI_Datatype, int, int, MPI_Comm);
int $mpi_recv(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Status*);
int $mpi_sendrecv(void* sendbuf, int sendcount, MPI_Datatype sendtype, int dest, int sendtag, void* recvbuf, int recvcount, MPI_Datatype recvtype, int source, int recvtag, MPI_Comm comm, MPI_Status* status);
int $mpi_collective_send(void*, int, MPI_Datatype, int, int, MPI_Comm);
int $mpi_collective_recv(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Status*, char*);
int $mpi_bcast(void*, int, MPI_Datatype, int, int, MPI_Comm, char*);
int $mpi_reduce(void*, void*, int, MPI_Datatype, MPI_Op, int, int, MPI_Comm, char*);
int $mpi_gather(void*, int, MPI_Datatype, void*, int, MPI_Datatype, int, int, MPI_Comm, char*);
int $mpi_gatherv(void*, int, MPI_Datatype, void*, int [], int [], MPI_Datatype, int, int, MPI_Comm, char*);
int $mpi_scatter(void*, int, MPI_Datatype, void*, int, MPI_Datatype, int, int, MPI_Comm, char*);
int $mpi_scatterv(void*, int [], int [], MPI_Datatype, void*, int, MPI_Datatype, int, int, MPI_Comm, char*);
void* $mpi_pointer_add(void*, int, MPI_Datatype);
$system[mpi] int $mpi_new_gcomm($scope, $mpi_gcomm);
$system[mpi] $mpi_gcomm $mpi_get_gcomm($scope, int);
int $mpi_comm_dup($scope, MPI_Comm, MPI_Comm*, char*);
int $mpi_comm_free(MPI_Comm*, $mpi_state);
$system[mpi] $scope $mpi_root_scope($comm);
$system[mpi] $scope $mpi_proc_scope($comm);
$system[mpi] void $mpi_check_buffer(void* buf, int count, MPI_Datatype datatype);
$bundle $mpi_create_coroutine_entry(int routineTag, int root, int op, int numDatatypes, int* datatypes);
void $mpi_diff_coroutine_entries($bundle specEntry, $bundle mineEntry, int rank);
void $mpi_coassert(MPI_Comm, _Bool);
_Bool $mpi_isRecvBufEmpty(int x);
/*@ depends_on \nothing;
  @*/
$system[mpi] void $mpi_p2pSendShot(int commID, $message msg, int place);
/*@ depends_on \nothing;
  @*/
$system[mpi] void $mpi_colSendShot(int commID, $message msg, int place);
/*@ depends_on \nothing;
  @*/
$system[mpi] void $mpi_p2pRecvShot(int commID, int source, int dest, int tag);
/*@ depends_on \nothing;
  @*/
$system[mpi] void $mpi_colRecvShot(int commID, int source, int dest, int tag);
//======================== stdlib.h ========================
typedef struct _div_t{
    int quot;
    int rem;
} div_t;
typedef struct _ldiv_t{
    long quot;
    long rem;
} ldiv_t;
typedef struct _lldiv_t{
    long long quot;
    long long rem;
} lldiv_t;
double atof(char* nptr);
int atoi(char* nptr);
long atol(char* nptr);
long long atoll(char* nptr);
double strtod(char* restrict nptr, char** restrict endptr);
float strtof(char* restrict nptr, char** restrict endptr);
long double strtold(char* restrict nptr, char** restrict endptr);
long strtol(char* restrict nptr, char** restrict endptr, int base);
long long strtoll(char* restrict nptr, char** restrict endptr, int base);
unsigned long strtoul(char* restrict nptr, char** restrict endptr, int base);
unsigned long long strtoull(char* restrict nptr, char** restrict endptr, int base);
$system[stdlib] int rand(void);
$system[stdlib] void srand(unsigned seed);
$system[stdlib] long random(void);
$system[stdlib] void srandom(unsigned seed);
void* aligned_alloc(size_t alignment, size_t size);
void* calloc(size_t nmemb, size_t size);
$system[stdlib] void free(void* ptr);
$system[stdlib] void* malloc(size_t size);
void* realloc(void* ptr, size_t size);
_Noreturn void abort(void);
int atexit( (void (void))* func);
int at_quick_exit( (void (void))* func);
$system[stdlib] void exit(int status);
_Noreturn void _Exit(int status);
char* getenv(char* name);
_Noreturn void quick_exit(int status);
int system(char* string);
void* bsearch(void* key, void* base, size_t nmemb, size_t size,  (int (void*, void*))* compar);
void qsort(void* base, size_t nmemb, size_t size,  (int (void*, void*))* compar);
int abs(int j);
long labs(long j);
long long llabs(long long j);
div_t div(int numer, int denom);
ldiv_t ldiv(long numer, long denom);
lldiv_t lldiv(long long numer, long long denom);
int mblen(char* s, size_t n);
int mbtowc(wchar_t* restrict pwc, char* restrict s, size_t n);
int wctomb(char* s, wchar_t wchar);
size_t mbstowcs(wchar_t* restrict pwcs, char* restrict s, size_t n);
size_t wcstombs(char* restrict s, wchar_t* restrict pwcs, size_t n);
typedef int errno_t;
typedef size_t rsize_t;
typedef  (void (char* restrict msg, void* restrict ptr, errno_t error))* constraint_handler_t;
constraint_handler_t set_constraint_handler_s(constraint_handler_t handler);
void abort_handler_s(char* restrict msg, void* restrict ptr, errno_t error);
void ignore_handler_s(char* restrict msg, void* restrict ptr, errno_t error);
errno_t getenv_s(size_t* restrict len, char* restrict value, rsize_t maxsize, char* restrict name);
void* bsearch_s(void* key, void* base, rsize_t nmemb, rsize_t size,  (int (void* k, void* y, void* context))* compar, void* context);
errno_t qsort_s(void* base, rsize_t nmemb, rsize_t size,  (int (void* x, void* y, void* context))* compar, void* context);
errno_t wctomb_s(int* restrict status, char* restrict s, rsize_t smax, wchar_t wc);
errno_t mbstowcs_s(size_t* restrict retval, wchar_t* restrict dst, rsize_t dstmax, char* restrict src, rsize_t len);
errno_t wcstombs_s(size_t* restrict retval, char* restrict dst, rsize_t dstmax, wchar_t* restrict src, rsize_t len);
//======================= pointer.cvh ======================
/*@ depends_on \write(obj);
  @ executes_when $true;
  @*/
$system[pointer] void $set_default(void* obj);
/*@ depends_on \write(obj1, obj2, result);
  @ executes_when $true;
  @*/
$system[pointer] void $apply(void* obj1, $operation op, void* obj2, void* result);
/*@ depends_on \write(x, y);
  @ executes_when $true;
  @*/
$system[pointer] _Bool $equals(void* x, void* y);
/*@ depends_on \write(x, y);
  @ executes_when $true;
  @*/
$system[pointer] void $assert_equals(void* x, void* y, ...);
/*@ depends_on \write(obj1, obj2);
  @ executes_when $true;
  @*/
$system[pointer] _Bool $contains(void* obj1, void* obj2);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[pointer] void* $translate_ptr(void* ptr, void* obj);
/*@ depends_on \write(ptr, value);
  @ executes_when $true;
  @*/
$system[pointer] void $copy(void* ptr, void* value);
/*@ depends_on \write(array);
  @ executes_when $true;
  @*/
$system[pointer] void $leaf_node_ptrs(void* array, void* obj);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[pointer] _Bool $is_identity_ref(void* obj);
/*@ depends_on \write(obj);
  @ executes_when $true;
  @*/
$system[pointer] void $set_leaf_nodes(void* obj, int value);
/*@ depends_on \write(obj);
  @ executes_when $true;
  @*/
$system[pointer] _Bool $leaf_nodes_equal_to(void* obj, int value);
/*@ depends_on \write(obj);
  @ executes_when $true;
  @*/
$system[pointer] _Bool $has_leaf_node_equal_to(void* obj, int value);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[pointer] _Bool $is_derefable_pointer(void* ptr);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[pointer] void* $pointer_add(void* ptr, int offset, int type_size);
//========================= mpi.cvl ========================
struct MPI_Request{
    MPI_Status status;
    _Bool isSend;
};
struct MPI_Comm{
    $comm p2p;
    $comm col;
    $collator collator;
    $barrier barrier;
    int gcommIndex;
};
$mpi_state _mpi_state = _MPI_UNINIT;
int $mpi_init(void)
{
  $assert(_mpi_state == _MPI_UNINIT, "Process can only call MPI_Init() at most once.");
  _mpi_state = _MPI_INIT;
  return 0;
}
int MPI_Finalize(void)
{
  $assert(_mpi_state == _MPI_INIT, "Process can only call MPI_Finalize() after the MPI enviroment is created and before cleaned.");
  _mpi_state = _MPI_FINALIZED;
  return 0;
}
double MPI_Wtime()
{
  double result;
  int CMPI_time_count = $next_time_count();
  $assert(_mpi_state == _MPI_INIT, "MPI_Wtime() cannot be invoked without MPI_Init() being called before.\n");
  result = $mpi_time(CMPI_time_count);
  if (CMPI_time_count > 0)
  {
    $assume(result > $mpi_time(CMPI_time_count - 1));
  }
  else
  {
    $assume(result > 0);
  }
  return result;
}
int MPI_Comm_size(MPI_Comm comm, int* size)
{
  $assert(_mpi_state == _MPI_INIT, "MPI_Comm_size() cannot be invoked without MPI_Init() being called before.\n");
  *size = $comm_size(comm.p2p);
  return 0;
}
int MPI_Comm_rank(MPI_Comm comm, int* rank)
{
  $assert(_mpi_state == _MPI_INIT, "MPI_Comm_rank() cannot be invoked without MPI_Init() being called before.\n");
  *rank = $comm_place(comm.p2p);
  return 0;
}
int MPI_Send(void* buf, int count, MPI_Datatype datatype, int dest, int tag, MPI_Comm comm)
{
  $assert(_mpi_state == _MPI_INIT, "MPI_Send() cannot be invoked without MPI_Init() being called before.\n");
  $mpi_check_buffer(buf, count, datatype);
  return $mpi_send(buf, count, datatype, dest, tag, comm);
}
int MPI_Recv(void* buf, int count, MPI_Datatype datatype, int source, int tag, MPI_Comm comm, MPI_Status* status)
{
  $assert(_mpi_state == _MPI_INIT, "MPI_Recv() cannot be invoked without MPI_Init() being called before.\n");
  return $mpi_recv(buf, count, datatype, source, tag, comm, status);
}
int MPI_Get_count(MPI_Status* status, MPI_Datatype datatype, int* count)
{
  $assert(_mpi_state == _MPI_INIT, "MPI_Get_count() cannot be invoked without MPI_Init() being called before.\n");
  *count = (status)->size / sizeofDatatype(datatype);
  return 0;
}
int MPI_Get_processor_name(char* name, int* resultlen)
{
  $abstract int MPI_GET_PROCESSOR_NAME(char*, int*);
  return MPI_GET_PROCESSOR_NAME(name, resultlen);
}
int MPI_Sendrecv(void* sendbuf, int sendcount, MPI_Datatype sendtype, int dest, int sendtag, void* recvbuf, int recvcount, MPI_Datatype recvtype, int source, int recvtag, MPI_Comm comm, MPI_Status* status)
{
  $assert(_mpi_state == _MPI_INIT, "MPI_Sendrecv() cannot be invoked without MPI_Init() being called before.\n");
  $mpi_check_buffer(sendbuf, sendcount, sendtype);
  $mpi_sendrecv(sendbuf, sendcount, sendtype, dest, sendtag, recvbuf, recvcount, recvtype, source, recvtag, comm, status);
  return 0;
}
int MPI_Bcast(void* buf, int count, MPI_Datatype datatype, int root, MPI_Comm comm)
{
  int place = $comm_place(comm.col);
  int nprocs = $comm_size(comm.col);
  int  datatypes[1] = {(int)datatype};
  $bundle checkerEntry;
  $bundle specEntry;
  $assert(_mpi_state == _MPI_INIT, "MPI_Bcast() cannot be invoked without MPI_Init() being called before.\n");
  if (place == root)
    $mpi_check_buffer(buf, count, datatype);
  checkerEntry = $mpi_create_coroutine_entry(9999, root, -1, 1, datatypes);
  specEntry = $collator_check(comm.collator, place, nprocs, checkerEntry);
  $mpi_diff_coroutine_entries(specEntry, checkerEntry, place);
  $mpi_bcast(buf, count, datatype, root, 9999, comm, "MPI_Bcast()");
  return 0;
}
int MPI_Reduce(void* sendbuf, void* recvbuf, int count, MPI_Datatype datatype, MPI_Op op, int root, MPI_Comm comm)
{
  int place = $comm_place(comm.col);
  int nprocs = $comm_size(comm.col);
  int  datatypes[1] = {(int)datatype};
  $bundle checkerEntry;
  $bundle specEntry;
  $assert(_mpi_state == _MPI_INIT, "MPI_Reduce() cannot be invoked without MPI_Init() being called before.\n");
  checkerEntry = $mpi_create_coroutine_entry(9998, root, (int)op, 1, datatypes);
  specEntry = $collator_check(comm.collator, place, nprocs, checkerEntry);
  $mpi_diff_coroutine_entries(specEntry, checkerEntry, place);
  $mpi_check_buffer(sendbuf, count, datatype);
  $mpi_reduce(sendbuf, recvbuf, count, datatype, op, root, 9998, comm, "MPI_Reduce()");
  return 0;
}
int MPI_Allreduce(void* sendbuf, void* recvbuf, int count, MPI_Datatype datatype, MPI_Op op, MPI_Comm comm)
{
  int root = 0;
  int place = $comm_place(comm.col);
  int nprocs = $comm_size(comm.col);
  int  datatypes[1] = {(int)datatype};
  MPI_Status status;
  $bundle checkerEntry;
  $bundle specEntry;
  $assert(_mpi_state == _MPI_INIT, "MPI_Allreduce() cannot be invoked without MPI_Init() being called before.\n");
  $mpi_check_buffer(sendbuf, count, datatype);
  checkerEntry = $mpi_create_coroutine_entry(9997, root, (int)op, 1, datatypes);
  specEntry = $collator_check(comm.collator, place, nprocs, checkerEntry);
  $mpi_diff_coroutine_entries(specEntry, checkerEntry, place);
  $mpi_reduce(sendbuf, recvbuf, count, datatype, op, root, 9997, comm, "MPI_Allreduce()");
  $mpi_bcast(recvbuf, count, datatype, root, 9997, comm, "MPI_Allreduce()");
  return 0;
}
int MPI_Barrier(MPI_Comm comm)
{
  int place = $comm_place(comm.col);
  int nprocs = $comm_size(comm.col);
  $bundle checkerEntry;
  $bundle specEntry;
  $assert(_mpi_state == _MPI_INIT, "MPI_Barrier() cannot be invoked without MPI_Init() being called before.\n");
  checkerEntry = $mpi_create_coroutine_entry(9987, 0, -1, 0, (void*)0);
  specEntry = $collator_check(comm.collator, place, nprocs, checkerEntry);
  $mpi_diff_coroutine_entries(specEntry, checkerEntry, place);
  $barrier_call(comm.barrier);
  return 0;
}
int MPI_Gather(void* sendbuf, int sendcount, MPI_Datatype sendtype, void* recvbuf, int recvcount, MPI_Datatype recvtype, int root, MPI_Comm comm)
{
  int place = $comm_place(comm.col);
  int nprocs = $comm_size(comm.col);
  int  datatypes[2] = {(int)sendtype, (int)recvtype};
  $bundle checkerEntry;
  $bundle specEntry;
  $assert(_mpi_state == _MPI_INIT, "MPI_Gather() cannot be invoked without MPI_Init() being called before.\n");
  if (sendbuf != (void*)(-1))
    $mpi_check_buffer(sendbuf, sendcount, sendtype);
  checkerEntry = $mpi_create_coroutine_entry(9996, root, -1, 2, datatypes);
  specEntry = $collator_check(comm.collator, place, nprocs, checkerEntry);
  $mpi_diff_coroutine_entries(specEntry, checkerEntry, place);
  $mpi_gather(sendbuf, sendcount, sendtype, recvbuf, recvcount, recvtype, root, 9996, comm, "MPI_Gather()");
  return 0;
}
int MPI_Scatter(void* sendbuf, int sendcount, MPI_Datatype sendtype, void* recvbuf, int recvcount, MPI_Datatype recvtype, int root, MPI_Comm comm)
{
  int place = $comm_place(comm.col);
  int nprocs = $comm_size(comm.col);
  int  datatypes[2] = {(int)sendtype, (int)recvtype};
  $bundle checkerEntry;
  $bundle specEntry;
  $assert(_mpi_state == _MPI_INIT, "MPI_Scatter() cannot be invoked without MPI_Init() being called before.\n");
  if (place == root)
    $mpi_check_buffer(sendbuf, sendcount, sendtype);
  checkerEntry = $mpi_create_coroutine_entry(9995, root, -1, 2, datatypes);
  specEntry = $collator_check(comm.collator, place, nprocs, checkerEntry);
  $mpi_diff_coroutine_entries(specEntry, checkerEntry, place);
  $mpi_scatter(sendbuf, sendcount, sendtype, recvbuf, recvcount, recvtype, root, 9995, comm, "MPI_Scatter()");
  return 0;
}
int MPI_Gatherv(void* sendbuf, int sendcount, MPI_Datatype sendtype, void* recvbuf, int  recvcounts[], int  displs[], MPI_Datatype recvtype, int root, MPI_Comm comm)
{
  int place = $comm_place(comm.col);
  int nprocs = $comm_size(comm.col);
  int  datatypes[2] = {(int)sendtype, (int)recvtype};
  int recvcount = 0;
  $bundle checkerEntry;
  $bundle specEntry;
  $assert(_mpi_state == _MPI_INIT, "MPI_Gatherv() cannot be invoked without MPI_Init() being called before.\n");
  if (sendbuf != (void*)(-1))
    $mpi_check_buffer(sendbuf, sendcount, sendtype);
  checkerEntry = $mpi_create_coroutine_entry(9994, root, -1, 2, datatypes);
  specEntry = $collator_check(comm.collator, place, nprocs, checkerEntry);
  $mpi_diff_coroutine_entries(specEntry, checkerEntry, place);
  $mpi_gatherv(sendbuf, sendcount, sendtype, recvbuf, recvcounts, displs, recvtype, root, 9994, comm, "MPI_Gatherv()");
  return 0;
}
int MPI_Scatterv(void* sendbuf, int  sendcounts[], int  displs[], MPI_Datatype sendtype, void* recvbuf, int recvcount, MPI_Datatype recvtype, int root, MPI_Comm comm)
{
  int place = $comm_place(comm.col);
  int nprocs = $comm_size(comm.col);
  int  datatypes[2] = {(int)sendtype, (int)recvtype};
  int sendcount = 0;
  $bundle checkerEntry;
  $bundle specEntry;
  $assert(_mpi_state == _MPI_INIT, "MPI_Scatterv() cannot be invoked without MPI_Init() being called before.\n");
  if (place == root)
  {
    for (int i = 0; i < nprocs; i++)
      sendcount += sendcounts[i];
    $mpi_check_buffer(sendbuf, sendcount, sendtype);
  }
  checkerEntry = $mpi_create_coroutine_entry(9993, root, -1, 2, datatypes);
  specEntry = $collator_check(comm.collator, place, nprocs, checkerEntry);
  $mpi_diff_coroutine_entries(specEntry, checkerEntry, place);
  $mpi_scatterv(sendbuf, sendcounts, displs, sendtype, recvbuf, recvcount, recvtype, root, 9993, comm, "MPI_Scatterv()");
  return 0;
}
int MPI_Allgather(void* sendbuf, int sendcount, MPI_Datatype sendtype, void* recvbuf, int recvcount, MPI_Datatype recvtype, MPI_Comm comm)
{
  int place = $comm_place(comm.col);
  int nprocs = $comm_size(comm.col);
  int  datatypes[2] = {(int)sendtype, (int)recvtype};
  $bundle checkerEntry;
  $bundle specEntry;
  $assert(_mpi_state == _MPI_INIT, "MPI_Allgather() cannot be invoked without MPI_Init() being called before.\n");
  if (sendbuf != (void*)(-1))
    $mpi_check_buffer(sendbuf, sendcount, sendtype);
  checkerEntry = $mpi_create_coroutine_entry(9992, 0, -1, 2, datatypes);
  specEntry = $collator_check(comm.collator, place, nprocs, checkerEntry);
  $mpi_diff_coroutine_entries(specEntry, checkerEntry, place);
  $mpi_gather(sendbuf, sendcount, sendtype, recvbuf, recvcount, recvtype, 0, 9992, comm, "MPI_Allgather()");
  $mpi_bcast(recvbuf, recvcount * nprocs, recvtype, 0, 9992, comm, "MPI_Allgather()");
  return 0;
}
int MPI_Reduce_scatter(void* sendbuf, void* recvbuf, int  recvcount[], MPI_Datatype datatype, MPI_Op op, MPI_Comm comm)
{
  int total_count;
  int i;
  int nprocs = $comm_size(comm.col);
  int rank = $comm_place(comm.col);
  int root = 0;
  int  displs[nprocs];
  int  datatypes[1] = {(int)datatype};
  $bundle checkerEntry;
  $bundle specEntry;
  $assert(_mpi_state == _MPI_INIT, "MPI_Reduce_scatter() cannot be invoked without MPI_Init() being called before.\n");
  $mpi_check_buffer(sendbuf, recvcount[rank], datatype);
  for (total_count = 0, i = 0; i < nprocs; i++)
  {
    displs[i] = total_count;
    total_count += recvcount[i];
  }
  checkerEntry = $mpi_create_coroutine_entry(9991, root, (int)op, 1, datatypes);
  specEntry = $collator_check(comm.collator, rank, nprocs, checkerEntry);
  $mpi_diff_coroutine_entries(specEntry, checkerEntry, rank);
  $mpi_reduce(sendbuf, sendbuf, total_count, datatype, op, root, 9991, comm, "MPI_Reduce_scatter()");
  $mpi_scatterv(sendbuf, recvcount, displs, datatype, recvbuf, recvcount[rank], datatype, root, 9991, comm, "MPI_Reduce_scatter()");
  return 0;
}
int MPI_Alltoall(void* sendbuf, int sendcount, MPI_Datatype sendtype, void* recvbuf, int recvcount, MPI_Datatype recvtype, MPI_Comm comm)
{
  int nprocs = $comm_size(comm.col);
  int rank = $comm_place(comm.col);
  int root = 0;
  int  displs[nprocs];
  int  sendcounts[nprocs];
  int  datatypes[2] = {(int)sendtype, (int)recvtype};
  $bundle checkerEntry;
  $bundle specEntry;
  for (int i = 0; i < nprocs; i++)
  {
    sendcounts[i] = sendcount;
    displs[i] = i == 0 ? 0 : (displs[i - 1]) + sendcount;
  }
  $assert(_mpi_state == _MPI_INIT, "MPI_Alltoall() cannot be invoked without MPI_Init() being called before.\n");
  $mpi_check_buffer(sendbuf, sendcount * nprocs, sendtype);
  checkerEntry = $mpi_create_coroutine_entry(9990, root, -1, 2, datatypes);
  specEntry = $collator_check(comm.collator, rank, nprocs, checkerEntry);
  $mpi_diff_coroutine_entries(specEntry, checkerEntry, rank);
  for (int i = 0; i < nprocs; i++)
  {
    void* ptr = $mpi_pointer_add(recvbuf, i * sendcount, recvtype);
    $mpi_scatterv(sendbuf, sendcounts, displs, sendtype, ptr, recvcount, recvtype, i, 9990, comm, "MPI_Alltoall()");
  }
  return 0;
}
int MPI_Alltoallv(void* sendbuf, int  sendcounts[], int  sdispls[], MPI_Datatype sendtype, void* recvbuf, int  recvcounts[], int  rdispls[], MPI_Datatype recvtype, MPI_Comm comm)
{
  int nprocs = $comm_size(comm.col);
  int place = $comm_place(comm.col);
  int  datatypes[2] = {(int)sendtype, (int)recvtype};
  int sendcount = 0;
  int recvcount = 0;
  $bundle checkerEntry;
  $bundle specEntry;
  $assert(_mpi_state == _MPI_INIT, "MPI_Alltoallv() cannot be invoked without MPI_Init() being called before.\n");
  for (int i = 0; i < nprocs; i++)
  {
    sendcount += sendcounts[i];
    recvcount += recvcounts[i];
  }
  $mpi_check_buffer(sendbuf, sendcount, sendtype);
  checkerEntry = $mpi_create_coroutine_entry(9989, 0, -1, 2, datatypes);
  specEntry = $collator_check(comm.collator, place, nprocs, checkerEntry);
  $mpi_diff_coroutine_entries(specEntry, checkerEntry, place);
  for (int i = 0; i < nprocs; i++)
  {
    void* ptr = $mpi_pointer_add(recvbuf, rdispls[i], recvtype);
    $mpi_scatterv(sendbuf, sendcounts, sdispls, sendtype, ptr, recvcounts[i], recvtype, i, 9989, comm, "MPI_Alltoallv()");
  }
  return 0;
}
int MPI_Alltoallw(void* sendbuf, int  sendcounts[], int  sdispls[], MPI_Datatype  sendtypes[], void* recvbuf, int  recvcounts[], int  rdispls[], MPI_Datatype  recvtypes[], MPI_Comm comm)
{
  int nprocs = $comm_size(comm.col);
  int place = $comm_place(comm.col);
  $assert(_mpi_state == _MPI_INIT, "MPI_Alltoallw() cannot be invoked without MPI_Init() being called before.\n");
  for (int i = 0; i < nprocs; i++)
  {
    void* ptr = $mpi_pointer_add(recvbuf, rdispls[i], recvtypes[i]);
    void* sendptr = $mpi_pointer_add(sendbuf, sdispls[i], sendtypes[i]);
    $mpi_check_buffer(sendptr, sendcounts[i], sendtypes[i]);
    $mpi_scatterv(sendbuf, sendcounts, sdispls, sendtypes[i], ptr, recvcounts[i], recvtypes[i], i, 9988, comm, "MPI_Alltoallw()");
  }
  return 0;
}
int MPI_Comm_dup(MPI_Comm comm, MPI_Comm* newcomm)
{
  $scope CMPI_PROC_SCOPE = $mpi_proc_scope(comm.col);
  $assert(_mpi_state == _MPI_INIT, "MPI_Comm_dup() cannot be invoked without MPI_Init() being called before.\n");
  $mpi_comm_dup(CMPI_PROC_SCOPE, comm, newcomm, "MPI_Comm_dup");
  return 0;
}
int MPI_Comm_free(MPI_Comm* comm)
{
  $assert(_mpi_state == _MPI_INIT, "MPI_Comm_free() cannot be invoked without MPI_Init() being called before.\n");
  $assert($is_derefable_pointer(comm), "The argument of MPI_Comm_free is NULL.");
  $mpi_comm_free(comm, _mpi_state);
  return 0;
}
int MPI_Init_thread(int* argc, char*** argv, int required, int* provided)
{
  _mpi_state = _MPI_INIT;
  *provided = 3;
  return 0;
}
//======================== civlc.cvh =======================
$system[civlc] void $wait($proc p);
$system[civlc] void $waitall($proc* procs, int numProcs);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $exit(void);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] int $choose_int(int n);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $assert(_Bool expr, ...);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $assume(_Bool expr);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $elaborate(int x);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] int $next_time_count(void);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $pathCondition(void);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] _Bool $is_concrete_int(int value);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void* $malloc($scope s, int size);
/*@ depends_on \write(p);
  @ executes_when $true;
  @*/
$system[civlc] void $free(void* p);
/*@ depends_on \write(ptr);
  @ executes_when $true;
  @*/
$system[civlc] void $havoc(void* ptr);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] double $pow(double base, double exp);
//======================= bundle.cvh =======================
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[bundle] int $bundle_size($bundle b);
/*@ depends_on \write(ptr);
  @ executes_when $true;
  @*/
$system[bundle] $bundle $bundle_pack(void* ptr, int size);
/*@ depends_on \write(ptr);
  @ executes_when $true;
  @*/
$system[bundle] void $bundle_unpack($bundle bundle, void* ptr);
/*@ depends_on \write(buf);
  @ executes_when $true;
  @*/
$system[bundle] void $bundle_unpack_apply($bundle data, void* buf, int size, $operation op);
//===================== concurrency.cvh ====================
/*@ depends_on \nothing;
  @ assigns \nothing;
  @ reads \nothing;
  @*/
$atomic_f $gbarrier $gbarrier_create($scope scope, int size);
/*@ depends_on \write(gbarrier);
  @ reads \nothing;
  @ assigns gbarrier;
  @*/
$atomic_f void $gbarrier_destroy($gbarrier gbarrier);
/*@ depends_on \nothing;
  @ assigns gbarrier;
  @ reads gbarrier;
  @*/
$atomic_f $barrier $barrier_create($scope scope, $gbarrier gbarrier, int place);
/*@ depends_on \write(barrier);
  @ assigns barrier;
  @ reads \nothing;
  @*/
$atomic_f void $barrier_destroy($barrier barrier);
void $barrier_call($barrier barrier);
/*@ depends_on \nothing;
  @ reads \nothing;
  @ assigns \nothing;
  @*/
$atomic_f $gcollator $gcollator_create($scope scope);
/*@ depends_on \write(gcollator);
  @ assigns gcollator;
  @ reads \nothing;
  @*/
$atomic_f int $gcollator_destroy($gcollator gcollator);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f $collator $collator_create($scope scope, $gcollator gcollator);
/*@ depends_on \write(collator);
  @ executes_when $true;
  @*/
$atomic_f void $collator_destroy($collator collator);
/*@ depends_on \write(collator);
  @ executes_when $true;
  @*/
$system[concurrency] $bundle $collator_check($collator collator, int place, int nprocs, $bundle entries);
//======================== comm.cvh ========================
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f $message $message_pack(int source, int dest, int tag, void* data, int size);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f int $message_source($message message);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f int $message_tag($message message);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f int $message_dest($message message);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f int $message_size($message message);
/*@ depends_on \write(buf);
  @ executes_when $true;
  @*/
$atomic_f void $message_unpack($message message, void* buf, int size);
/*@ depends_on \nothing;
  @ assigns \nothing;
  @ reads \nothing;
  @*/
$atomic_f $gcomm $gcomm_create($scope scope, int size);
/*@ depends_on \write(junkMsgs), \write(gcomm);
  @ assigns junkMsgs, gcomm;
  @*/
$atomic_f int $gcomm_destroy($gcomm gcomm, void* junkMsgs);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[comm] void $gcomm_dup($comm comm, $comm newcomm);
$atomic_f $comm $comm_create($scope scope, $gcomm gcomm, int place);
/*@ depends_on \write(comm);
  @ assigns comm;
  @ reads \nothing;
  @*/
$atomic_f void $comm_destroy($comm comm);
/*@ pure;
  @ depends_on \nothing;
  @*/
$atomic_f int $comm_size($comm comm);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f int $comm_place($comm comm);
/*@ depends_on \write(comm);
  @ executes_when $true;
  @*/
$system[comm] void $comm_enqueue($comm comm, $message message);
/*@ pure;
  @ depends_on \write(comm);
  @ executes_when $true;
  @*/
$system[comm] _Bool $comm_probe($comm comm, int source, int tag);
/*@ pure;
  @ depends_on \write(comm);
  @ executes_when $true;
  @*/
$system[comm] $message $comm_seek($comm comm, int source, int tag);
/*@ depends_on \write(comm);
  @ executes_when $comm_probe(comm, source, tag);
  @*/
$system[comm] $message $comm_dequeue($comm comm, int source, int tag);
//========================== mpi.h =========================
MPI_Comm MPI_COMM_WORLD;
MPI_Comm MPI_COMM_SELF;
MPI_Comm MPI_COMM_PARENT;
MPI_Comm MPI_COMM_TYPE_SHARED;
int MPI_Send(void*, int, MPI_Datatype, int, int, MPI_Comm);
int MPI_Recv(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Status*);
int MPI_Get_count(MPI_Status*, MPI_Datatype, int*);
int MPI_Bsend(void*, int, MPI_Datatype, int, int, MPI_Comm);
int MPI_Ssend(void*, int, MPI_Datatype, int, int, MPI_Comm);
int MPI_Rsend(void*, int, MPI_Datatype, int, int, MPI_Comm);
int MPI_Buffer_attach(void*, int);
int MPI_Buffer_detach(void*, int*);
int MPI_Isend(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Ibsend(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Issend(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Irsend(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Irecv(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Wait(MPI_Request*, MPI_Status*);
int MPI_Test(MPI_Request*, int*, MPI_Status*);
int MPI_Request_free(MPI_Request*);
int MPI_Waitany(int, MPI_Request*, int*, MPI_Status*);
int MPI_Testany(int, MPI_Request*, int*, int*, MPI_Status*);
int MPI_Waitall(int, MPI_Request*, MPI_Status*);
int MPI_Testall(int, MPI_Request*, int*, MPI_Status*);
int MPI_Waitsome(int, MPI_Request*, int*, int*, MPI_Status*);
int MPI_Testsome(int, MPI_Request*, int*, int*, MPI_Status*);
int MPI_Iprobe(int, int, MPI_Comm, int*, MPI_Status*);
int MPI_Probe(int, int, MPI_Comm, MPI_Status*);
int MPI_Cancel(MPI_Request*);
int MPI_Test_cancelled(MPI_Status*, int*);
int MPI_Send_init(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Bsend_init(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Ssend_init(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Rsend_init(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Recv_init(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request*);
int MPI_Start(MPI_Request*);
int MPI_Startall(int, MPI_Request*);
int MPI_Sendrecv(void*, int, MPI_Datatype, int, int, void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Status*);
int MPI_Sendrecv_replace(void*, int, MPI_Datatype, int, int, int, int, MPI_Comm, MPI_Status*);
int MPI_Type_contiguous(int, MPI_Datatype, MPI_Datatype*);
int MPI_Type_vector(int, int, int, MPI_Datatype, MPI_Datatype*);
int MPI_Type_hvector(int, int, MPI_Aint, MPI_Datatype, MPI_Datatype*);
int MPI_Type_indexed(int, int*, int*, MPI_Datatype, MPI_Datatype*);
int MPI_Type_hindexed(int, int*, MPI_Aint*, MPI_Datatype, MPI_Datatype*);
int MPI_Type_struct(int, int*, MPI_Aint*, MPI_Datatype*, MPI_Datatype*);
int MPI_Address(void*, MPI_Aint*);
int MPI_Type_extent(MPI_Datatype, MPI_Aint*);
int MPI_Type_size(MPI_Datatype, int*);
int MPI_Type_lb(MPI_Datatype, MPI_Aint*);
int MPI_Type_ub(MPI_Datatype, MPI_Aint*);
int MPI_Type_commit(MPI_Datatype*);
int MPI_Type_free(MPI_Datatype*);
int MPI_Get_elements(MPI_Status*, MPI_Datatype, int*);
int MPI_Pack(void*, int, MPI_Datatype, void*, int, int*, MPI_Comm);
int MPI_Unpack(void*, int, int*, void*, int, MPI_Datatype, MPI_Comm);
int MPI_Pack_size(int, MPI_Datatype, MPI_Comm, int*);
int MPI_Barrier(MPI_Comm);
int MPI_Bcast(void*, int, MPI_Datatype, int, MPI_Comm);
int MPI_Gather(void*, int, MPI_Datatype, void*, int, MPI_Datatype, int, MPI_Comm);
int MPI_Gatherv(void*, int, MPI_Datatype, void*, int*, int*, MPI_Datatype, int, MPI_Comm);
int MPI_Scatter(void*, int, MPI_Datatype, void*, int, MPI_Datatype, int, MPI_Comm);
int MPI_Scatterv(void*, int*, int*, MPI_Datatype, void*, int, MPI_Datatype, int, MPI_Comm);
int MPI_Allgather(void*, int, MPI_Datatype, void*, int, MPI_Datatype, MPI_Comm);
int MPI_Allgatherv(void*, int, MPI_Datatype, void*, int*, int*, MPI_Datatype, MPI_Comm);
int MPI_Alltoall(void*, int, MPI_Datatype, void*, int, MPI_Datatype, MPI_Comm);
int MPI_Alltoallv(void*, int*, int*, MPI_Datatype, void*, int*, int*, MPI_Datatype, MPI_Comm);
int MPI_Reduce(void*, void*, int, MPI_Datatype, MPI_Op, int, MPI_Comm);
int MPI_Op_create(MPI_User_function*, int, MPI_Op*);
int MPI_Op_free(MPI_Op*);
int MPI_Allreduce(void*, void*, int, MPI_Datatype, MPI_Op, MPI_Comm);
int MPI_Reduce_scatter(void*, void*, int*, MPI_Datatype, MPI_Op, MPI_Comm);
int MPI_Scan(void*, void*, int, MPI_Datatype, MPI_Op, MPI_Comm);
int MPI_Group_size(MPI_Group, int*);
int MPI_Group_rank(MPI_Group, int*);
int MPI_Group_translate_ranks(MPI_Group, int, int*, MPI_Group, int*);
int MPI_Group_compare(MPI_Group, MPI_Group, int*);
int MPI_Comm_group(MPI_Comm, MPI_Group*);
int MPI_Group_union(MPI_Group, MPI_Group, MPI_Group*);
int MPI_Group_intersection(MPI_Group, MPI_Group, MPI_Group*);
int MPI_Group_difference(MPI_Group, MPI_Group, MPI_Group*);
int MPI_Group_incl(MPI_Group, int, int*, MPI_Group*);
int MPI_Group_excl(MPI_Group, int, int*, MPI_Group*);
int MPI_Group_range_incl(MPI_Group, int, int [][3], MPI_Group*);
int MPI_Group_range_excl(MPI_Group, int, int [][3], MPI_Group*);
int MPI_Group_free(MPI_Group*);
int MPI_Comm_size(MPI_Comm, int*);
int MPI_Comm_rank(MPI_Comm, int*);
int MPI_Comm_compare(MPI_Comm, MPI_Comm, int*);
int MPI_Comm_dup(MPI_Comm, MPI_Comm*);
int MPI_Comm_create(MPI_Comm, MPI_Group, MPI_Comm*);
int MPI_Comm_split(MPI_Comm, int, int, MPI_Comm*);
int MPI_Comm_free(MPI_Comm*);
int MPI_Comm_test_inter(MPI_Comm, int*);
int MPI_Comm_remote_size(MPI_Comm, int*);
int MPI_Comm_remote_group(MPI_Comm, MPI_Group*);
int MPI_Intercomm_create(MPI_Comm, int, MPI_Comm, int, int, MPI_Comm*);
int MPI_Intercomm_merge(MPI_Comm, int, MPI_Comm*);
int MPI_Keyval_create(MPI_Copy_function*, MPI_Delete_function*, int*, void*);
int MPI_Keyval_free(int*);
int MPI_Attr_put(MPI_Comm, int, void*);
int MPI_Attr_get(MPI_Comm, int, void*, int*);
int MPI_Attr_delete(MPI_Comm, int);
int MPI_Topo_test(MPI_Comm, int*);
int MPI_Cart_create(MPI_Comm, int, int*, int*, int, MPI_Comm*);
int MPI_Dims_create(int, int, int*);
int MPI_Graph_create(MPI_Comm, int, int*, int*, int, MPI_Comm*);
int MPI_Graphdims_get(MPI_Comm, int*, int*);
int MPI_Graph_get(MPI_Comm, int, int, int*, int*);
int MPI_Cartdim_get(MPI_Comm, int*);
int MPI_Cart_get(MPI_Comm, int, int*, int*, int*);
int MPI_Cart_rank(MPI_Comm, int*, int*);
int MPI_Cart_coords(MPI_Comm, int, int, int*);
int MPI_Graph_neighbors_count(MPI_Comm, int, int*);
int MPI_Graph_neighbors(MPI_Comm, int, int, int*);
int MPI_Cart_shift(MPI_Comm, int, int, int*, int*);
int MPI_Cart_sub(MPI_Comm, int*, MPI_Comm*);
int MPI_Cart_map(MPI_Comm, int, int*, int*, int*);
int MPI_Graph_map(MPI_Comm, int, int*, int*, int*);
int MPI_Get_processor_name(char*, int*);
int MPI_Get_version(int*, int*);
int MPI_Errhandler_create(MPI_Handler_function*, MPI_Errhandler*);
int MPI_Errhandler_set(MPI_Comm, MPI_Errhandler);
int MPI_Errhandler_get(MPI_Comm, MPI_Errhandler*);
int MPI_Errhandler_free(MPI_Errhandler*);
int MPI_Error_string(int, char*, int*);
int MPI_Error_class(int, int*);
double MPI_Wtime(void);
double MPI_Wtick(void);
int MPI_Init(int*, char***);
int MPI_Finalize(void);
int MPI_Initialized(int*);
$system[mpi] int MPI_Abort(MPI_Comm, int);
int MPI_Pcontrol(const int, ...);
int MPI_DUP_FN(MPI_Comm, int, void*, void*, void*, int*);
int MPI_Close_port(char*);
int MPI_Comm_accept(char*, MPI_Info, int, MPI_Comm, MPI_Comm*);
int MPI_Comm_connect(char*, MPI_Info, int, MPI_Comm, MPI_Comm*);
int MPI_Comm_disconnect(MPI_Comm*);
int MPI_Comm_get_parent(MPI_Comm*);
int MPI_Comm_join(int, MPI_Comm*);
int MPI_Comm_spawn(char*, char* [], int, MPI_Info, int, MPI_Comm, MPI_Comm*, int []);
int MPI_Comm_spawn_multiple(int, char* [], char** [], int [], MPI_Info [], int, MPI_Comm, MPI_Comm*, int []);
int MPI_Lookup_name(char*, MPI_Info, char*);
int MPI_Open_port(MPI_Info, char*);
int MPI_Publish_name(char*, MPI_Info, char*);
int MPI_Unpublish_name(char*, MPI_Info, char*);
int MPI_Accumulate(void*, int, MPI_Datatype, int, MPI_Aint, int, MPI_Datatype, MPI_Op, MPI_Win);
int MPI_Get(void*, int, MPI_Datatype, int, MPI_Aint, int, MPI_Datatype, MPI_Win);
int MPI_Put(void*, int, MPI_Datatype, int, MPI_Aint, int, MPI_Datatype, MPI_Win);
int MPI_Win_complete(MPI_Win);
int MPI_Win_create(void*, MPI_Aint, int, MPI_Info, MPI_Comm, MPI_Win*);
int MPI_Win_fence(int, MPI_Win);
int MPI_Win_free(MPI_Win*);
int MPI_Win_get_group(MPI_Win, MPI_Group*);
int MPI_Win_lock(int, int, int, MPI_Win);
int MPI_Win_post(MPI_Group, int, MPI_Win);
int MPI_Win_start(MPI_Group, int, MPI_Win);
int MPI_Win_test(MPI_Win, int*);
int MPI_Win_unlock(int, MPI_Win);
int MPI_Win_wait(MPI_Win);
int MPI_Alltoallw(void*, int [], int [], MPI_Datatype [], void*, int [], int [], MPI_Datatype [], MPI_Comm);
int MPI_Exscan(void*, void*, int, MPI_Datatype, MPI_Op, MPI_Comm);
int MPI_Add_error_class(int*);
int MPI_Add_error_code(int, int*);
int MPI_Add_error_string(int, char*);
int MPI_Comm_call_errhandler(MPI_Comm, int);
int MPI_Comm_create_keyval(MPI_Comm_copy_attr_function*, MPI_Comm_delete_attr_function*, int*, void*);
int MPI_Comm_delete_attr(MPI_Comm, int);
int MPI_Comm_free_keyval(int*);
int MPI_Comm_get_attr(MPI_Comm, int, void*, int*);
int MPI_Comm_get_name(MPI_Comm, char*, int*);
int MPI_Comm_set_attr(MPI_Comm, int, void*);
int MPI_Comm_set_name(MPI_Comm, char*);
int MPI_File_call_errhandler(MPI_File, int);
int MPI_Grequest_complete(MPI_Request);
int MPI_Grequest_start(MPI_Grequest_query_function*, MPI_Grequest_free_function*, MPI_Grequest_cancel_function*, void*, MPI_Request*);
int MPI_Init_thread(int*, char***, int, int*);
int MPI_Is_thread_main(int*);
int MPI_Query_thread(int*);
int MPI_Status_set_cancelled(MPI_Status*, int);
int MPI_Status_set_elements(MPI_Status*, MPI_Datatype, int);
int MPI_Type_create_keyval(MPI_Type_copy_attr_function*, MPI_Type_delete_attr_function*, int*, void*);
int MPI_Type_delete_attr(MPI_Datatype, int);
int MPI_Type_dup(MPI_Datatype, MPI_Datatype*);
int MPI_Type_free_keyval(int*);
int MPI_Type_get_attr(MPI_Datatype, int, void*, int*);
int MPI_Type_get_contents(MPI_Datatype, int, int, int, int [], MPI_Aint [], MPI_Datatype []);
int MPI_Type_get_envelope(MPI_Datatype, int*, int*, int*, int*);
int MPI_Type_get_name(MPI_Datatype, char*, int*);
int MPI_Type_set_attr(MPI_Datatype, int, void*);
int MPI_Type_set_name(MPI_Datatype, char*);
int MPI_Type_match_size(int, int, MPI_Datatype*);
int MPI_Win_call_errhandler(MPI_Win, int);
int MPI_Win_create_keyval(MPI_Win_copy_attr_function*, MPI_Win_delete_attr_function*, int*, void*);
int MPI_Win_delete_attr(MPI_Win, int);
int MPI_Win_free_keyval(int*);
int MPI_Win_get_attr(MPI_Win, int, void*, int*);
int MPI_Win_get_name(MPI_Win, char*, int*);
int MPI_Win_set_attr(MPI_Win, int, void*);
int MPI_Win_set_name(MPI_Win, char*);
MPI_Comm MPI_Comm_f2c(MPI_Fint);
MPI_Datatype MPI_Type_f2c(MPI_Fint);
MPI_File MPI_File_f2c(MPI_Fint);
MPI_Fint MPI_Comm_c2f(MPI_Comm);
MPI_Fint MPI_File_c2f(MPI_File);
MPI_Fint MPI_Group_c2f(MPI_Group);
MPI_Fint MPI_Info_c2f(MPI_Info);
MPI_Fint MPI_Op_c2f(MPI_Op);
MPI_Fint MPI_Request_c2f(MPI_Request);
MPI_Fint MPI_Type_c2f(MPI_Datatype);
MPI_Fint MPI_Win_c2f(MPI_Win);
MPI_Group MPI_Group_f2c(MPI_Fint);
MPI_Info MPI_Info_f2c(MPI_Fint);
MPI_Op MPI_Op_f2c(MPI_Fint);
MPI_Request MPI_Request_f2c(MPI_Fint);
MPI_Win MPI_Win_f2c(MPI_Fint);
int MPI_Alloc_mem(MPI_Aint, MPI_Info info, void* baseptr);
int MPI_Comm_create_errhandler(MPI_Comm_errhandler_function*, MPI_Errhandler*);
int MPI_Comm_get_errhandler(MPI_Comm, MPI_Errhandler*);
int MPI_Comm_set_errhandler(MPI_Comm, MPI_Errhandler);
int MPI_File_create_errhandler(MPI_File_errhandler_function*, MPI_Errhandler*);
int MPI_File_get_errhandler(MPI_File, MPI_Errhandler*);
int MPI_File_set_errhandler(MPI_File, MPI_Errhandler);
int MPI_Finalized(int*);
int MPI_Free_mem(void*);
int MPI_Get_address(void*, MPI_Aint*);
int MPI_Info_create(MPI_Info*);
int MPI_Info_delete(MPI_Info, char*);
int MPI_Info_dup(MPI_Info, MPI_Info*);
int MPI_Info_free(MPI_Info* info);
int MPI_Info_get(MPI_Info, char*, int, char*, int*);
int MPI_Info_get_nkeys(MPI_Info, int*);
int MPI_Info_get_nthkey(MPI_Info, int, char*);
int MPI_Info_get_valuelen(MPI_Info, char*, int*, int*);
int MPI_Info_set(MPI_Info, char*, char*);
int MPI_Pack_external(char*, void*, int, MPI_Datatype, void*, MPI_Aint, MPI_Aint*);
int MPI_Pack_external_size(char*, int, MPI_Datatype, MPI_Aint*);
int MPI_Request_get_status(MPI_Request, int*, MPI_Status*);
int MPI_Status_c2f(MPI_Status*, MPI_Fint*);
int MPI_Status_f2c(MPI_Fint*, MPI_Status*);
int MPI_Type_create_darray(int, int, int, int [], int [], int [], int [], int, MPI_Datatype, MPI_Datatype*);
int MPI_Type_create_hindexed(int, int [], MPI_Aint [], MPI_Datatype, MPI_Datatype*);
int MPI_Type_create_hvector(int, int, MPI_Aint, MPI_Datatype, MPI_Datatype*);
int MPI_Type_create_indexed_block(int, int, int [], MPI_Datatype, MPI_Datatype*);
int MPIX_Type_create_hindexed_block(int, int, MPI_Aint [], MPI_Datatype, MPI_Datatype*);
int MPI_Type_create_resized(MPI_Datatype, MPI_Aint, MPI_Aint, MPI_Datatype*);
int MPI_Type_create_struct(int, int [], MPI_Aint [], MPI_Datatype [], MPI_Datatype*);
int MPI_Type_create_subarray(int, int [], int [], int [], int, MPI_Datatype, MPI_Datatype*);
int MPI_Type_get_extent(MPI_Datatype, MPI_Aint*, MPI_Aint*);
int MPI_Type_get_true_extent(MPI_Datatype, MPI_Aint*, MPI_Aint*);
int MPI_Unpack_external(char*, void*, MPI_Aint, MPI_Aint*, void*, int, MPI_Datatype);
int MPI_Win_create_errhandler(MPI_Win_errhandler_function*, MPI_Errhandler*);
int MPI_Win_get_errhandler(MPI_Win, MPI_Errhandler*);
int MPI_Win_set_errhandler(MPI_Win, MPI_Errhandler);
int MPI_Type_create_f90_integer(int, MPI_Datatype*);
int MPI_Type_create_f90_real(int, int, MPI_Datatype*);
int MPI_Type_create_f90_complex(int, int, MPI_Datatype*);
int MPI_Reduce_local(void* inbuf, void* inoutbuf, int count, MPI_Datatype datatype, MPI_Op op);
int MPI_Op_commutative(MPI_Op op, int* commute);
int MPI_Reduce_scatter_block(void* sendbuf, void* recvbuf, int recvcount, MPI_Datatype datatype, MPI_Op op, MPI_Comm comm);
int MPI_Dist_graph_create_adjacent(MPI_Comm comm_old, int indegree, int [], int [], int outdegree, int [], int [], MPI_Info info, int reorder, MPI_Comm* comm_dist_graph);
int MPI_Dist_graph_create(MPI_Comm comm_old, int n, int [], int [], int [], int [], MPI_Info info, int reorder, MPI_Comm* comm_dist_graph);
int MPI_Dist_graph_neighbors_count(MPI_Comm comm, int* indegree, int* outdegree, int* weighted);
int MPI_Dist_graph_neighbors(MPI_Comm comm, int maxindegree, int [], int [], int maxoutdegree, int [], int []);
const extern int* MPI_UNWEIGHTED;
extern MPI_Fint* MPI_F_STATUS_IGNORE;
extern MPI_Fint* MPI_F_STATUSES_IGNORE;
const extern struct MPIR_T_pvar_handle* MPI_T_PVAR_ALL_HANDLES;
//====================== civl-mpi.cvh ======================
int sizeofDatatype(MPI_Datatype);
$abstract double $mpi_time(int i);
$mpi_gcomm $mpi_gcomm_create($scope, int);
void $mpi_gcomm_destroy($mpi_gcomm);
MPI_Comm $mpi_comm_create($scope, $mpi_gcomm, int);
void $mpi_comm_destroy(MPI_Comm, $mpi_state);
int $mpi_send(void*, int, MPI_Datatype, int, int, MPI_Comm);
int $mpi_recv(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Status*);
int $mpi_sendrecv(void* sendbuf, int sendcount, MPI_Datatype sendtype, int dest, int sendtag, void* recvbuf, int recvcount, MPI_Datatype recvtype, int source, int recvtag, MPI_Comm comm, MPI_Status* status);
int $mpi_collective_send(void*, int, MPI_Datatype, int, int, MPI_Comm);
int $mpi_collective_recv(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Status*, char*);
int $mpi_bcast(void*, int, MPI_Datatype, int, int, MPI_Comm, char*);
int $mpi_reduce(void*, void*, int, MPI_Datatype, MPI_Op, int, int, MPI_Comm, char*);
int $mpi_gather(void*, int, MPI_Datatype, void*, int, MPI_Datatype, int, int, MPI_Comm, char*);
int $mpi_gatherv(void*, int, MPI_Datatype, void*, int [], int [], MPI_Datatype, int, int, MPI_Comm, char*);
int $mpi_scatter(void*, int, MPI_Datatype, void*, int, MPI_Datatype, int, int, MPI_Comm, char*);
int $mpi_scatterv(void*, int [], int [], MPI_Datatype, void*, int, MPI_Datatype, int, int, MPI_Comm, char*);
void* $mpi_pointer_add(void*, int, MPI_Datatype);
$system[mpi] int $mpi_new_gcomm($scope, $mpi_gcomm);
$system[mpi] $mpi_gcomm $mpi_get_gcomm($scope, int);
int $mpi_comm_dup($scope, MPI_Comm, MPI_Comm*, char*);
int $mpi_comm_free(MPI_Comm*, $mpi_state);
$system[mpi] $scope $mpi_root_scope($comm);
$system[mpi] $scope $mpi_proc_scope($comm);
$system[mpi] void $mpi_check_buffer(void* buf, int count, MPI_Datatype datatype);
$bundle $mpi_create_coroutine_entry(int routineTag, int root, int op, int numDatatypes, int* datatypes);
void $mpi_diff_coroutine_entries($bundle specEntry, $bundle mineEntry, int rank);
void $mpi_coassert(MPI_Comm, _Bool);
_Bool $mpi_isRecvBufEmpty(int x);
/*@ depends_on \nothing;
  @*/
$system[mpi] void $mpi_p2pSendShot(int commID, $message msg, int place);
/*@ depends_on \nothing;
  @*/
$system[mpi] void $mpi_colSendShot(int commID, $message msg, int place);
/*@ depends_on \nothing;
  @*/
$system[mpi] void $mpi_p2pRecvShot(int commID, int source, int dest, int tag);
/*@ depends_on \nothing;
  @*/
$system[mpi] void $mpi_colRecvShot(int commID, int source, int dest, int tag);
//======================== string.h ========================
void* memcpy(void* p, void* q, size_t size);
void* memmove(void* dest, void* src, size_t n);
$system[string] void* memset(void* s, int c, size_t n);
int memcmp(void* s1, void* s2, size_t n);
void* memchr(void* s, int c, size_t n);
$system[string] char* strcpy(char* restrict s1, char* restrict s2);
char* strncpy(char* dest, char* src, size_t n);
char* strcat(char* dest, char* src);
char* strncat(char* dest, char* src, size_t n);
$system[string] int strcmp(char* s1, char* s2);
int strncmp(char* s1, char* s2, size_t n);
int strcoll(char* s1, char* s2);
size_t strxfrm(char* dest, char* src, size_t n);
char* strchr(char* s, int c);
char* strrchr(char* s, int c);
size_t strcspn(char* s, char* reject);
size_t strspn(char* s, char* accept);
char* strpbrk(char* s, char* accept);
char* strstr(char* s1, char* s2);
char* strtok(char* s, char* delim);
$system[string] size_t strlen(char* s);
char* strerror(int errnum);
//======================= pointer.cvh ======================
/*@ depends_on \write(obj);
  @ executes_when $true;
  @*/
$system[pointer] void $set_default(void* obj);
/*@ depends_on \write(obj1, obj2, result);
  @ executes_when $true;
  @*/
$system[pointer] void $apply(void* obj1, $operation op, void* obj2, void* result);
/*@ depends_on \write(x, y);
  @ executes_when $true;
  @*/
$system[pointer] _Bool $equals(void* x, void* y);
/*@ depends_on \write(x, y);
  @ executes_when $true;
  @*/
$system[pointer] void $assert_equals(void* x, void* y, ...);
/*@ depends_on \write(obj1, obj2);
  @ executes_when $true;
  @*/
$system[pointer] _Bool $contains(void* obj1, void* obj2);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[pointer] void* $translate_ptr(void* ptr, void* obj);
/*@ depends_on \write(ptr, value);
  @ executes_when $true;
  @*/
$system[pointer] void $copy(void* ptr, void* value);
/*@ depends_on \write(array);
  @ executes_when $true;
  @*/
$system[pointer] void $leaf_node_ptrs(void* array, void* obj);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[pointer] _Bool $is_identity_ref(void* obj);
/*@ depends_on \write(obj);
  @ executes_when $true;
  @*/
$system[pointer] void $set_leaf_nodes(void* obj, int value);
/*@ depends_on \write(obj);
  @ executes_when $true;
  @*/
$system[pointer] _Bool $leaf_nodes_equal_to(void* obj, int value);
/*@ depends_on \write(obj);
  @ executes_when $true;
  @*/
$system[pointer] _Bool $has_leaf_node_equal_to(void* obj, int value);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[pointer] _Bool $is_derefable_pointer(void* ptr);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[pointer] void* $pointer_add(void* ptr, int offset, int type_size);
//========================= seq.cvh ========================
/*@ depends_on \write(array);
  @ executes_when $true;
  @*/
$system[seq] int $seq_length(void* array);
/*@ depends_on \write(array, value);
  @ executes_when $true;
  @*/
$system[seq] void $seq_init(void* array, int count, void* value);
/*@ depends_on \write(array, values);
  @ executes_when $true;
  @*/
$system[seq] void $seq_insert(void* array, int index, void* values, int count);
/*@ depends_on \write(array, values);
  @ executes_when $true;
  @*/
$system[seq] void $seq_remove(void* array, int index, void* values, int count);
/*@ depends_on \write(array, values);
  @*/
$atomic_f void $seq_append(void* array, void* values, int count);
//====================== civl-mpi.cvl ======================
char* getCoroutineName(int tag);
struct $mpi_gcomm{
    $gcomm p2p;
    $gcomm col;
    $gcollator gcollator;
    $gbarrier gbarrier;
};
int sizeofDatatype(MPI_Datatype datatype)
{
  switch (datatype)
  {
    case MPI_INT:
      return sizeof(int);
    case MPI_2INT:
      return sizeof(int) * 2;
    case MPI_FLOAT:
      return sizeof(float);
    case MPI_DOUBLE:
      return sizeof(double);
    case MPI_CHAR:
      return sizeof(char);
    case MPI_BYTE:
      return sizeof(char);
    case MPI_SHORT:
      return sizeof(short);
    case MPI_LONG:
      return sizeof(long);
    case MPI_LONG_DOUBLE:
      return sizeof(long double);
    case MPI_LONG_LONG_INT:
      return sizeof(long long);
    case MPI_LONG_LONG:
      return sizeof(long long);
    case MPI_UNSIGNED_LONG_LONG:
      return sizeof(unsigned long long);
    default:
      $assert(0, "Unreachable");
  }
}
$mpi_gcomm $mpi_gcomm_create($scope scope, int size)
{
  $mpi_gcomm result;
  result.p2p = $gcomm_create(scope, size);
  result.col = $gcomm_create(scope, size);
  result.gcollator = $gcollator_create(scope);
  result.gbarrier = $gbarrier_create(scope, size);
  return result;
}
void $mpi_gcomm_destroy($mpi_gcomm gc)
{
  int numJunkRecord;
  int numJunkMsg;
  $message  junkMsgs[];
  $seq_init(&(junkMsgs), 0, (void*)0);
  numJunkMsg = $gcomm_destroy(gc.p2p, &(junkMsgs));
  for (int i = 0; i < numJunkMsg; i++)
  {
    int src;
    int dest;
    int tag;
    src = $message_source(junkMsgs[i]);
    dest = $message_dest(junkMsgs[i]);
    tag = $message_tag(junkMsgs[i]);
    $assert($false, "MPI message leak: There is a message from rank %d to rank %d with tag %d has been sent but is never received in point-to-point communication.", src, dest, tag);
  }
  numJunkMsg = $gcomm_destroy(gc.col, &(junkMsgs));
  for (int i = 0; i < numJunkMsg; i++)
  {
    int src;
    int tag;
    char* routine;
    src = $message_source(junkMsgs[i]);
    tag = $message_tag(junkMsgs[i]);
    routine = getCoroutineName(tag);
    $assert($false, "MPI message leak: There is a message sent by rank %d for collective routine %s that is never received.", src, routine);
  }
  numJunkRecord = $gcollator_destroy(gc.gcollator);
  $gbarrier_destroy(gc.gbarrier);
  $assert(numJunkRecord == 0, "MPI collective routines are called inappropriately because there are %d collective records still remaining the collective routine checker.", numJunkRecord);
}
MPI_Comm $mpi_comm_create($scope scope, $mpi_gcomm gc, int rank)
{
  MPI_Comm result;
  result.p2p = $comm_create(scope, gc.p2p, rank);
  result.col = $comm_create(scope, gc.col, rank);
  result.collator = $collator_create(scope, gc.gcollator);
  result.barrier = $barrier_create(scope, gc.gbarrier, rank);
  result.gcommIndex = 0;
  return result;
}
void $mpi_comm_destroy(MPI_Comm comm, $mpi_state mpi_state)
{
  if (comm.gcommIndex == 0)
    $assert(mpi_state == _MPI_FINALIZED, "Process terminates without calling MPI_Finalize() first.");
  $comm_destroy(comm.p2p);
  $comm_destroy(comm.col);
  $collator_destroy(comm.collator);
  $barrier_destroy(comm.barrier);
}
void* $mpi_pointer_add(void* ptr, int offset, MPI_Datatype datatype)
{
  int type_size = sizeofDatatype(datatype);
  return $pointer_add(ptr, offset, type_size);
}
int $mpi_send(void* buf, int count, MPI_Datatype datatype, int dest, int tag, MPI_Comm comm)
{
  if (dest >= 0)
  {
    int size = count * sizeofDatatype(datatype);
    int place = $comm_place(comm.p2p);
    $message out = $message_pack(place, dest, tag, buf, size);
    $comm_enqueue(comm.p2p, out);
  }
  return 0;
}
int $mpi_recv(void* buf, int count, MPI_Datatype datatype, int source, int tag, MPI_Comm comm, MPI_Status* status)
{
  if ((source >= 0) || (source == (-1)))
  {
    $message in;
    int place = $comm_place(comm.p2p);
    int deterministicTag;
    $assert((tag == (-2)) || (tag >= 0), "Illegal MPI message receive tag %d.\n", tag);
    deterministicTag = tag < 0 ? -2 : tag;
    $elaborate(source);
    in = $comm_dequeue(comm.p2p, source, deterministicTag);
    int size = count * sizeofDatatype(datatype);
    $message_unpack(in, buf, size);
    if (status != (void*)0)
    {
      (status)->size = $message_size(in);
      (status)->MPI_SOURCE = $message_source(in);
      (status)->MPI_TAG = $message_tag(in);
      (status)->MPI_ERROR = 0;
    }
  }
  return 0;
}
int $mpi_sendrecv(void* sendbuf, int sendcount, MPI_Datatype sendtype, int dest, int sendtag, void* recvbuf, int recvcount, MPI_Datatype recvtype, int source, int recvtag, MPI_Comm comm, MPI_Status* status)
{
  int deterministicRecvTag;
  $assert(sendtag >= 0, "MPI sendtag should be greater than or equal to zero");
  $assert((recvtag == (-2)) || (recvtag >= 0), "Illegal MPI message receive tag %d.\n", recvtag);
  deterministicRecvTag = recvtag < 0 ? -2 : recvtag;
  if ((dest >= 0) && ((source >= 0) || (source == (-1))))
  {
    $message out;
    $message in;
    int size = sendcount * sizeofDatatype(sendtype);
    int place = $comm_place(comm.p2p);
    out = $message_pack(place, dest, sendtag, sendbuf, size);
    $elaborate(source);
    $choose{
      $when ($true)
      {
        $atomic
        {
          $comm_enqueue(comm.p2p, out);
        }
        $atomic
        {
          in = $comm_dequeue(comm.p2p, source, deterministicRecvTag);
        }
      }
      $when ($false)
      {
        in = $comm_dequeue(comm.p2p, source, deterministicRecvTag);
        $comm_enqueue(comm.p2p, out);
      }
    }
    size = recvcount * sizeofDatatype(recvtype);
    $message_unpack(in, recvbuf, size);
    if (status != (void*)0)
    {
      (status)->size = $message_size(in);
      (status)->MPI_SOURCE = $message_source(in);
      (status)->MPI_TAG = $message_tag(in);
      (status)->MPI_ERROR = 0;
    }
  }
  else
    if (dest >= 0)
    {
      $mpi_send(sendbuf, sendcount, sendtype, dest, sendtag, comm);
    }
    else
      if ((source >= 0) || (source == (-1)))
      {
        $mpi_recv(recvbuf, recvcount, recvtype, source, deterministicRecvTag, comm, status);
      }
  return 0;
}
int $mpi_collective_send(void* buf, int count, MPI_Datatype datatype, int dest, int tag, MPI_Comm comm)
{
  if (dest >= 0)
  {
    int size = count * sizeofDatatype(datatype);
    int place = $comm_place(comm.col);
    $message out = $message_pack(place, dest, tag, buf, size);
    $comm_enqueue(comm.col, out);
  }
  return 0;
}
int $mpi_collective_recv(void* buf, int count, MPI_Datatype datatype, int source, int tag, MPI_Comm comm, MPI_Status* status, char* routName)
{
  if ((source >= 0) || (source == (-1)))
  {
    $elaborate(source);
    $message in = $comm_dequeue(comm.col, source, -2);
    int size = count * sizeofDatatype(datatype);
    int recvTag;
    recvTag = $message_tag(in);
    $assert(recvTag == tag, "Collective routine %s receives a message with a mismatched tag\n", routName);
    $message_unpack(in, buf, size);
    if (status != (void*)0)
    {
      (status)->size = $message_size(in);
      (status)->MPI_SOURCE = $message_source(in);
      (status)->MPI_TAG = recvTag;
      (status)->MPI_ERROR = 0;
    }
  }
  return 0;
}
int $mpi_bcast(void* buf, int count, MPI_Datatype datatype, int root, int tag, MPI_Comm comm, char* routName)
{
  if ($comm_place(comm.col) == root)
  {
    int nprocs = $comm_size(comm.col);
    for (int i = 0; i < nprocs; i++)
      if (i != root)
        $mpi_collective_send(buf, count, datatype, i, tag, comm);
  }
  else
    $mpi_collective_recv(buf, count, datatype, root, tag, comm, (void*)0, routName);
  return 0;
}
int $mpi_reduce(void* sendbuf, void* recvbuf, int count, MPI_Datatype datatype, MPI_Op op, int root, int tag, MPI_Comm comm, char* routName)
{
  int rank;
  rank = $comm_place(comm.col);
  if (rank != root)
    $mpi_collective_send(sendbuf, count, datatype, root, tag, comm);
  else
  {
    int nprocs = $comm_size(comm.col);
    int size;
    size = count * sizeofDatatype(datatype);
    memcpy(recvbuf, sendbuf, size);
    for (int i = 0; i < nprocs; i++)
    {
      if (i != root)
      {
        int colTag;
        $message in = $comm_dequeue(comm.col, i, -2);
        colTag = $message_tag(in);
        $assert(colTag == tag, "Collective routine %s receives a message with a mismatched tag\n", routName);
        $bundle_unpack_apply(in.data, recvbuf, count, op);
        $assert(in.size <= size, "Message of size %d exceeds the specified size %d.", in.size, size);
      }
    }
  }
  return 0;
}
int $mpi_gather(void* sendbuf, int sendcount, MPI_Datatype sendtype, void* recvbuf, int recvcount, MPI_Datatype recvtype, int root, int tag, MPI_Comm comm, char* routName)
{
  int rank;
  int nprocs;
  MPI_Status status;
  rank = $comm_place(comm.col);
  nprocs = $comm_size(comm.col);
  if (rank == root)
    $assert(sendtype == recvtype, "%s asks for equality between \'sendtype\' and \'recvtype\'.", routName);
  if (sendbuf == (void*)(-1))
  {
    $assert(root == rank, "Only root can replace 'sendbuf' with 'MPI_IN_PLACE'.");
  }
  else
    if (root == rank)
    {
      void* ptr;
      $assert(sendcount == recvcount, "Root process of routine %d without using MPI_IN_PLACE should give the same value for recvcount and sendcount", routName);
      ptr = $mpi_pointer_add(recvbuf, root * recvcount, recvtype);
      memcpy(ptr, sendbuf, recvcount * sizeofDatatype(recvtype));
    }
    else
      $mpi_collective_send(sendbuf, sendcount, sendtype, root, tag, comm);
  if (rank == root)
  {
    int real_recvcount;
    int offset;
    for (int i = 0; i < nprocs; i++)
    {
      if (i != root)
      {
        void* ptr;
        offset = i * recvcount;
        ptr = $mpi_pointer_add(recvbuf, offset, recvtype);
        $mpi_collective_recv(ptr, recvcount, recvtype, i, tag, comm, &(status), routName);
        real_recvcount = status.size / sizeofDatatype(recvtype);
        $assert(real_recvcount == recvcount, "%s asks for equality between the amount of data sent and the amount of data received.", routName);
      }
    }
  }
  return 0;
}
int $mpi_gatherv(void* sendbuf, int sendcount, MPI_Datatype sendtype, void* recvbuf, int  recvcounts[], int  displs[], MPI_Datatype recvtype, int root, int tag, MPI_Comm comm, char* routName)
{
  int rank;
  int nprocs;
  rank = $comm_place(comm.col);
  nprocs = $comm_size(comm.col);
  if (rank == root)
    $assert(sendtype == recvtype, "%s asks for equality between \'sendtype\' and \'recvtype\'.", routName);
  if (sendbuf == (void*)(-1))
  {
    $assert(root == rank, "Only root can replace 'sendbuf' with 'MPI_IN_PLACE'.");
  }
  else
    if (root == rank)
    {
      void* ptr;
      $assert(sendcount == (recvcounts[root]), "For routine %s, recvcounts[%d] should be same as the sendcount of the process with rank %d.\n", routName, root, root);
      ptr = $mpi_pointer_add(recvbuf, displs[rank], recvtype);
      memcpy(ptr, sendbuf, sendcount * sizeofDatatype(recvtype));
    }
    else
    {
      $mpi_collective_send(sendbuf, sendcount, sendtype, root, tag, comm);
    }
  if (rank == root)
  {
    int real_recvcount;
    MPI_Status status;
    for (int i = 0; i < nprocs; i++)
    {
      if (i != root)
      {
        void* ptr = $mpi_pointer_add(recvbuf, displs[i], recvtype);
        $mpi_collective_recv(ptr, recvcounts[i], recvtype, i, tag, comm, &(status), routName);
        real_recvcount = status.size / sizeofDatatype(recvtype);
        $assert(real_recvcount == (recvcounts[i]), "%s asks for equality between the amount of data sent and the amount of data received.", routName);
      }
    }
  }
  return 0;
}
int $mpi_scatter(void* sendbuf, int sendcount, MPI_Datatype sendtype, void* recvbuf, int recvcount, MPI_Datatype recvtype, int root, int tag, MPI_Comm comm, char* routName)
{
  int rank;
  int nprocs;
  rank = $comm_place(comm.col);
  nprocs = $comm_size(comm.col);
  if (rank == root)
    $assert(sendtype == recvtype, "MPI_Scatter() asks for equality between \'sendtype\' and \'recvtype\'.");
  if (recvbuf == (void*)(-1))
  {
    $assert(root == rank, "Only root can replace 'recvbuf' with 'MPI_IN_PLACE'.");
  }
  else
    if (rank == root)
    {
      void* ptr;
      $assert(sendcount == recvcount, "Root process of routine %d without using MPI_IN_PLACE should give the same value for recvcount and sendcount", routName);
      ptr = $mpi_pointer_add(sendbuf, root * recvcount, sendtype);
      memcpy(recvbuf, ptr, sizeofDatatype(recvtype) * recvcount);
    }
  if (rank == root)
  {
    int offset;
    for (int i = 0; i < nprocs; i++)
    {
      if (i != root)
      {
        void* ptr;
        offset = i * sendcount;
        ptr = $mpi_pointer_add(sendbuf, offset, sendtype);
        $mpi_collective_send(ptr, sendcount, sendtype, i, tag, comm);
      }
    }
  }
  if (!(root == rank))
  {
    int real_recvcount;
    MPI_Status status;
    $mpi_collective_recv(recvbuf, recvcount, recvtype, root, tag, comm, &(status), routName);
    real_recvcount = status.size / sizeofDatatype(recvtype);
    $assert(real_recvcount == recvcount, "%s asks for equality between the amount of data sent and the amount of data received.", routName);
  }
  return 0;
}
int $mpi_scatterv(void* sendbuf, int  sendcounts[], int  displs[], MPI_Datatype sendtype, void* recvbuf, int recvcount, MPI_Datatype recvtype, int root, int tag, MPI_Comm comm, char* routName)
{
  int rank;
  int nprocs;
  rank = $comm_place(comm.col);
  nprocs = $comm_size(comm.col);
  if (rank == root)
    $assert(sendtype == recvtype, "%s asks for equality between \'sendtype\' and \'recvtype\'.", routName);
  if (recvbuf == (void*)(-1))
  {
    $assert(root == rank, "Only root can replace 'recvbuf' with 'MPI_IN_PLACE'.");
  }
  else
    if (rank == root)
    {
      void* ptr;
      $assert((sendcounts[root]) == recvcount, "For routine %s, sendcounts[%d] should be same as the recvcount of the process with rank %d.\n", routName, root, root);
      ptr = $mpi_pointer_add(sendbuf, displs[root], sendtype);
      memcpy(recvbuf, ptr, recvcount * sizeofDatatype(recvtype));
    }
  if (rank == root)
  {
    for (int i = 0; i < nprocs; i++)
    {
      if (i != root)
      {
        void* ptr = $mpi_pointer_add(sendbuf, displs[i], sendtype);
        $mpi_collective_send(ptr, sendcounts[i], sendtype, i, tag, comm);
      }
    }
  }
  if (!(root == rank))
  {
    MPI_Status status;
    int real_recvcount;
    $mpi_collective_recv(recvbuf, recvcount, recvtype, root, tag, comm, &(status), routName);
    real_recvcount = status.size / sizeofDatatype(recvtype);
    $assert(real_recvcount == recvcount, "Process rank:%d\n%s asks for equality between the amount of data sent (%d) and the amount of data received (%d).", rank, routName, real_recvcount, recvcount);
  }
  return 0;
}
int $mpi_comm_dup($scope scope, MPI_Comm comm, MPI_Comm* newcomm, char* routName)
{
  int place = $comm_place(comm.col);
  $mpi_gcomm newgcomm;
  int idx;
  $scope CMPI_ROOT_SCOPE = $mpi_root_scope(comm.col);
  if (place == 0)
  {
    int size = $comm_size(comm.col);
    newgcomm = $mpi_gcomm_create(CMPI_ROOT_SCOPE, size);
    idx = $mpi_new_gcomm(CMPI_ROOT_SCOPE, newgcomm);
  }
  $mpi_bcast(&(idx), 1, MPI_INT, 0, 9986, comm, routName);
  newgcomm = $mpi_get_gcomm(CMPI_ROOT_SCOPE, idx);
  *newcomm = $mpi_comm_create(scope, newgcomm, place);
  (newcomm)->gcommIndex = idx;
  $barrier_call(comm.barrier);
  $gcomm_dup(comm.p2p, (newcomm)->p2p);
  $gcomm_dup(comm.col, (newcomm)->col);
  $barrier_call(comm.barrier);
  return 0;
}
int $mpi_comm_free(MPI_Comm* comm, $mpi_state mpi_state)
{
  int place = $comm_place((comm)->col);
  int size = $comm_size((comm)->col);
  int  buf[size];
  int gcommIndex = (comm)->gcommIndex;
  $scope CMPI_ROOT_SCOPE = $mpi_root_scope((comm)->col);
  $mpi_gather(&(place), 1, MPI_INT, buf, 1, MPI_INT, 0, 9985, *comm, "MPI_Comm_free synchronization.");
  $mpi_comm_destroy(*comm, mpi_state);
  if (place == 0)
  {
    $mpi_gcomm temp = $mpi_get_gcomm(CMPI_ROOT_SCOPE, gcommIndex);
    $mpi_gcomm_destroy(temp);
  }
  return 0;
}
$bundle $mpi_create_coroutine_entry(int routineTag, int root, int op, int numDatatypes, int* datatypes)
{
  int zero = 0;
  $bundle bundledEntry;
  struct Entry{
    int routine_tag;
    int root;
    int op;
    int numTypes;
    int  datatypes[];
} entry;
  entry.routine_tag = routineTag;
  entry.root = root;
  entry.op = op;
  entry.numTypes = numDatatypes;
  $seq_init(&(entry.datatypes), numDatatypes, &(zero));
  for (int i = 0; i < numDatatypes; i++)
    entry.datatypes[i] = datatypes[i];
  bundledEntry = $bundle_pack(&(entry), sizeof(struct Entry));
  return bundledEntry;
}
void $mpi_diff_coroutine_entries($bundle specEntry, $bundle mineEntry, int rank)
{
  struct Entry{
    int routine_tag;
    int root;
    int op;
    int numTypes;
    int  datatypes[];
} spec;
  struct Entry mine;
  char* routine;
  int numTypes;
  $bundle_unpack(specEntry, &(spec));
  $bundle_unpack(mineEntry, &(mine));
  routine = getCoroutineName(spec.routine_tag);
  if (spec.routine_tag != mine.routine_tag)
  {
    char* mineRoutine = getCoroutineName(mine.routine_tag);
    $assert($false, "Process with rank %d reaches an MPI collective routine %s while at least one of others are collectively reaching %s.", rank, mineRoutine, routine);
  }
  else
    if (spec.root != mine.root)
    {
      $assert($false, "Process with rank %d reaches an MPI collective routine %s which has a different root with at least one of others.", rank, routine);
    }
    else
      if (spec.op != mine.op)
      {
        $assert($false, "Process with rank %d reaches an MPI collective routine %s which has a different MPI_Op with at least one of others", rank, routine);
      }
      else
        if (spec.numTypes != mine.numTypes)
        {
          $assert($false, "Process with rank %d reaches an MPI collective routine %s which has an inconsistent datatype specification with at least one of others", rank, routine);
        }
  numTypes = spec.numTypes;
  for (int i = 0; i < numTypes; i++)
    if ((spec.datatypes[i]) != (mine.datatypes[i]))
    {
      $assert($false, "Process with rank %d reaches an MPI collective routine %s which has an inconsistent datatype specification with at least one of others", rank, routine);
      break;
    }
}
char* getCoroutineName(int tag)
{
  switch (tag)
  {
    case 9999:
      return "MPI_Bcast";
    case 9998:
      return "MPI_Reduce";
    case 9997:
      return "MPI_Allreduce";
    case 9996:
      return "MPI_Gather";
    case 9995:
      return "MPI_Scatter";
    case 9994:
      return "MPI_Gatherv";
    case 9993:
      return "MPI_Scatterv";
    case 9992:
      return "MPI_Allgather";
    case 9991:
      return "MPI_Reduce_scatter";
    case 9990:
      return "MPI_Alltoall";
    case 9989:
      return "MPI_Alltoallv";
    case 9988:
      return "MPI_Alltoallw";
    case 9987:
      return "MPI_Barrier";
    case 9986:
      return "MPI_Commdup";
    case 9985:
      return "MPI_Commfree";
    default:
      $assert($false, "Internal Error: Unexpected MPI routine tag:%d.\n", tag);
  }
}
//======================== civlc.cvh =======================
$system[civlc] void $wait($proc p);
$system[civlc] void $waitall($proc* procs, int numProcs);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $exit(void);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] int $choose_int(int n);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $assert(_Bool expr, ...);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $assume(_Bool expr);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $elaborate(int x);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] int $next_time_count(void);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $pathCondition(void);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] _Bool $is_concrete_int(int value);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void* $malloc($scope s, int size);
/*@ depends_on \write(p);
  @ executes_when $true;
  @*/
$system[civlc] void $free(void* p);
/*@ depends_on \write(ptr);
  @ executes_when $true;
  @*/
$system[civlc] void $havoc(void* ptr);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] double $pow(double base, double exp);
//======================== civlc.cvl =======================
struct $int_iter{
    int size;
    int  content[];
    int index;
};
//======================== civlc.cvh =======================
$system[civlc] void $wait($proc p);
$system[civlc] void $waitall($proc* procs, int numProcs);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $exit(void);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] int $choose_int(int n);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $assert(_Bool expr, ...);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $assume(_Bool expr);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $elaborate(int x);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] int $next_time_count(void);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $pathCondition(void);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] _Bool $is_concrete_int(int value);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void* $malloc($scope s, int size);
/*@ depends_on \write(p);
  @ executes_when $true;
  @*/
$system[civlc] void $free(void* p);
/*@ depends_on \write(ptr);
  @ executes_when $true;
  @*/
$system[civlc] void $havoc(void* ptr);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] double $pow(double base, double exp);
//======================= bundle.cvh =======================
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[bundle] int $bundle_size($bundle b);
/*@ depends_on \write(ptr);
  @ executes_when $true;
  @*/
$system[bundle] $bundle $bundle_pack(void* ptr, int size);
/*@ depends_on \write(ptr);
  @ executes_when $true;
  @*/
$system[bundle] void $bundle_unpack($bundle bundle, void* ptr);
/*@ depends_on \write(buf);
  @ executes_when $true;
  @*/
$system[bundle] void $bundle_unpack_apply($bundle data, void* buf, int size, $operation op);
//======================== comm.cvh ========================
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f $message $message_pack(int source, int dest, int tag, void* data, int size);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f int $message_source($message message);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f int $message_tag($message message);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f int $message_dest($message message);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f int $message_size($message message);
/*@ depends_on \write(buf);
  @ executes_when $true;
  @*/
$atomic_f void $message_unpack($message message, void* buf, int size);
/*@ depends_on \nothing;
  @ assigns \nothing;
  @ reads \nothing;
  @*/
$atomic_f $gcomm $gcomm_create($scope scope, int size);
/*@ depends_on \write(junkMsgs), \write(gcomm);
  @ assigns junkMsgs, gcomm;
  @*/
$atomic_f int $gcomm_destroy($gcomm gcomm, void* junkMsgs);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[comm] void $gcomm_dup($comm comm, $comm newcomm);
$atomic_f $comm $comm_create($scope scope, $gcomm gcomm, int place);
/*@ depends_on \write(comm);
  @ assigns comm;
  @ reads \nothing;
  @*/
$atomic_f void $comm_destroy($comm comm);
/*@ pure;
  @ depends_on \nothing;
  @*/
$atomic_f int $comm_size($comm comm);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f int $comm_place($comm comm);
/*@ depends_on \write(comm);
  @ executes_when $true;
  @*/
$system[comm] void $comm_enqueue($comm comm, $message message);
/*@ pure;
  @ depends_on \write(comm);
  @ executes_when $true;
  @*/
$system[comm] _Bool $comm_probe($comm comm, int source, int tag);
/*@ pure;
  @ depends_on \write(comm);
  @ executes_when $true;
  @*/
$system[comm] $message $comm_seek($comm comm, int source, int tag);
/*@ depends_on \write(comm);
  @ executes_when $comm_probe(comm, source, tag);
  @*/
$system[comm] $message $comm_dequeue($comm comm, int source, int tag);
//========================= seq.cvh ========================
/*@ depends_on \write(array);
  @ executes_when $true;
  @*/
$system[seq] int $seq_length(void* array);
/*@ depends_on \write(array, value);
  @ executes_when $true;
  @*/
$system[seq] void $seq_init(void* array, int count, void* value);
/*@ depends_on \write(array, values);
  @ executes_when $true;
  @*/
$system[seq] void $seq_insert(void* array, int index, void* values, int count);
/*@ depends_on \write(array, values);
  @ executes_when $true;
  @*/
$system[seq] void $seq_remove(void* array, int index, void* values, int count);
/*@ depends_on \write(array, values);
  @*/
$atomic_f void $seq_append(void* array, void* values, int count);
//======================== comm.cvl ========================
struct _queue{
    int length;
    $message  messages[];
};
struct _gcomm{
    int nprocs;
    $proc  procs[];
    _Bool  isInit[];
    $queue  buf[][];
};
struct _comm{
    int place;
    $gcomm gcomm;
};
/*@ depends_on \write(data);
  @*/
$atomic_f $message $message_pack(int source, int dest, int tag, void* data, int size)
{
  $message result;
  result.source = source;
  result.dest = dest;
  result.tag = tag;
  result.data = $bundle_pack(data, size);
  result.size = size;
  return result;
}
int $message_source($message message)
{
  return message.source;
}
int $message_tag($message message)
{
  return message.tag;
}
int $message_dest($message message)
{
  return message.dest;
}
int $message_size($message message)
{
  return message.size;
}
/*@ depends_on \write(buf);
  @*/
$atomic_f void $message_unpack($message message, void* buf, int size)
{
  $bundle_unpack(message.data, buf);
  $assert(message.size <= size, "Message of size %d exceeds the specified size %d.", message.size, size);
}
/*@ depends_on \nothing;
  @ assigns \nothing;
  @ reads \nothing;
  @*/
$atomic_f $gcomm $gcomm_create($scope scope, int size)
{
  $gcomm gcomm = ($gcomm)($malloc(scope, sizeof(struct _gcomm)));
  $queue empty;
  empty.length = 0;
  $seq_init(&(empty.messages), 0, (void*)0);
  (gcomm)->nprocs = size;
  (gcomm)->procs = ($proc[size]) $lambda (int i) $proc_null;
  (gcomm)->isInit = (_Bool[size]) $lambda (int i) $false;
  (gcomm)->buf = ($queue[size][size]) $lambda (int i, j) empty;
  return gcomm;
}
/*@ depends_on \write(junkMsgs), \write(gcomm);
  @ assigns junkMsgs, gcomm;
  @ reads \nothing;
  @*/
$atomic_f int $gcomm_destroy($gcomm gcomm, void* junkMsgs)
{
  int nprocs = (gcomm)->nprocs;
  int numJunks = 0;
  if (junkMsgs != (void*)0)
  {
    for (int i = 0; i < nprocs; i++)
      for (int j = 0; j < nprocs; j++)
      {
        $queue queue = (gcomm)->buf[i][j];
        if (queue.length > 0)
          $seq_append(junkMsgs, queue.messages, queue.length);
      }
    numJunks = $seq_length(junkMsgs);
  }
  $free(gcomm);
  return numJunks;
}
/*@ depends_on \nothing;
  @ reads gcomm;
  @ assigns gcomm;
  @*/
$atomic_f $comm $comm_create($scope scope, $gcomm gcomm, int place)
{
  $assert(!((gcomm)->isInit[place]), "the place %d is already occupied in the global communicator!", place);
  $comm comm = ($comm)($malloc(scope, sizeof(struct _comm)));
  (gcomm)->procs[place] = $self;
  (gcomm)->isInit[place] = $true;
  (comm)->gcomm = gcomm;
  (comm)->place = place;
  return comm;
}
/*@ depends_on \write(comm);
  @ assigns comm;
  @ reads \nothing;
  @*/
$atomic_f void $comm_destroy($comm comm)
{
  $free(comm);
}
/*@ pure;
  @ depends_on \nothing;
  @*/
$atomic_f int $comm_place($comm comm)
{
  return (comm)->place;
}
/*@ pure;
  @ depends_on \nothing;
  @*/
$atomic_f int $comm_size($comm comm)
{
  return ((comm)->gcomm)->nprocs;
}
//======================== civlc.cvh =======================
$system[civlc] void $wait($proc p);
$system[civlc] void $waitall($proc* procs, int numProcs);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $exit(void);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] int $choose_int(int n);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $assert(_Bool expr, ...);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $assume(_Bool expr);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $elaborate(int x);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] int $next_time_count(void);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $pathCondition(void);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] _Bool $is_concrete_int(int value);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void* $malloc($scope s, int size);
/*@ depends_on \write(p);
  @ executes_when $true;
  @*/
$system[civlc] void $free(void* p);
/*@ depends_on \write(ptr);
  @ executes_when $true;
  @*/
$system[civlc] void $havoc(void* ptr);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] double $pow(double base, double exp);
//======================= bundle.cvh =======================
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[bundle] int $bundle_size($bundle b);
/*@ depends_on \write(ptr);
  @ executes_when $true;
  @*/
$system[bundle] $bundle $bundle_pack(void* ptr, int size);
/*@ depends_on \write(ptr);
  @ executes_when $true;
  @*/
$system[bundle] void $bundle_unpack($bundle bundle, void* ptr);
/*@ depends_on \write(buf);
  @ executes_when $true;
  @*/
$system[bundle] void $bundle_unpack_apply($bundle data, void* buf, int size, $operation op);
//===================== concurrency.cvh ====================
/*@ depends_on \nothing;
  @ assigns \nothing;
  @ reads \nothing;
  @*/
$atomic_f $gbarrier $gbarrier_create($scope scope, int size);
/*@ depends_on \write(gbarrier);
  @ reads \nothing;
  @ assigns gbarrier;
  @*/
$atomic_f void $gbarrier_destroy($gbarrier gbarrier);
/*@ depends_on \nothing;
  @ assigns gbarrier;
  @ reads gbarrier;
  @*/
$atomic_f $barrier $barrier_create($scope scope, $gbarrier gbarrier, int place);
/*@ depends_on \write(barrier);
  @ assigns barrier;
  @ reads \nothing;
  @*/
$atomic_f void $barrier_destroy($barrier barrier);
void $barrier_call($barrier barrier);
/*@ depends_on \nothing;
  @ reads \nothing;
  @ assigns \nothing;
  @*/
$atomic_f $gcollator $gcollator_create($scope scope);
/*@ depends_on \write(gcollator);
  @ assigns gcollator;
  @ reads \nothing;
  @*/
$atomic_f int $gcollator_destroy($gcollator gcollator);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f $collator $collator_create($scope scope, $gcollator gcollator);
/*@ depends_on \write(collator);
  @ executes_when $true;
  @*/
$atomic_f void $collator_destroy($collator collator);
/*@ depends_on \write(collator);
  @ executes_when $true;
  @*/
$system[concurrency] $bundle $collator_check($collator collator, int place, int nprocs, $bundle entries);
//========================= seq.cvh ========================
/*@ depends_on \write(array);
  @ executes_when $true;
  @*/
$system[seq] int $seq_length(void* array);
/*@ depends_on \write(array, value);
  @ executes_when $true;
  @*/
$system[seq] void $seq_init(void* array, int count, void* value);
/*@ depends_on \write(array, values);
  @ executes_when $true;
  @*/
$system[seq] void $seq_insert(void* array, int index, void* values, int count);
/*@ depends_on \write(array, values);
  @ executes_when $true;
  @*/
$system[seq] void $seq_remove(void* array, int index, void* values, int count);
/*@ depends_on \write(array, values);
  @*/
$atomic_f void $seq_append(void* array, void* values, int count);
//===================== concurrency.cvl ====================
struct _gbarrier{
    int nprocs;
    $proc  proc_map[];
    _Bool  in_barrier[];
    int num_in_barrier;
};
struct _barrier{
    int place;
    $gbarrier gbarrier;
};
struct _collator_entry{
    $bundle entries;
    _Bool  marks[];
    int numMarked;
};
struct _gcollator{
    int length;
    $collator_entry  entries[];
};
struct _collator{
    $gcollator gcollator;
};
/*@ depends_on \write(barrier);
  @ assigns \nothing;
  @ executes_when $true;
  @*/
$system[concurrency] void $barrier_enter($barrier barrier);
/*@ depends_on \write(barrier);
  @ assigns \nothing;
  @*/
$system[concurrency] void $barrier_exit($barrier barrier);
void $barrier_call($barrier barrier)
{
  $barrier_enter(barrier);
  $barrier_exit(barrier);
}
/*@ depends_on \nothing;
  @ assigns \nothing;
  @ reads \nothing;
  @*/
$atomic_f $gbarrier $gbarrier_create($scope scope, int size)
{
  $gbarrier gbarrier = ($gbarrier)($malloc(scope, sizeof(struct _gbarrier)));
  (gbarrier)->nprocs = size;
  (gbarrier)->proc_map = ($proc[size]) $lambda (int i) $proc_null;
  (gbarrier)->in_barrier = (_Bool[size]) $lambda (int i) $false;
  (gbarrier)->num_in_barrier = 0;
  return gbarrier;
}
/*@ depends_on \write(gbarrier);
  @ reads \nothing;
  @ assigns gbarrier;
  @*/
$atomic_f void $gbarrier_destroy($gbarrier gbarrier)
{
  $free(gbarrier);
}
/*@ depends_on \nothing;
  @ assigns gbarrier;
  @ reads gbarrier;
  @*/
$atomic_f $barrier $barrier_create($scope scope, $gbarrier gbarrier, int place)
{
  $assert(((gbarrier)->proc_map[place]) == $proc_null, "the place %d in the global barrier has already been taken.", place);
  $barrier barrier = ($barrier)($malloc(scope, sizeof(struct _barrier)));
  (barrier)->place = place;
  (barrier)->gbarrier = gbarrier;
  (gbarrier)->proc_map[place] = $self;
  return barrier;
}
/*@ depends_on \write(barrier);
  @ assigns barrier;
  @ reads \nothing;
  @*/
$atomic_f void $barrier_destroy($barrier barrier)
{
  $free(barrier);
}
/*@ depends_on \nothing;
  @ reads \nothing;
  @ assigns \nothing;
  @*/
$atomic_f $gcollator $gcollator_create($scope scope)
{
  $gcollator gcollator = ($gcollator)($malloc(scope, sizeof(struct _gcollator)));
  (gcollator)->length = 0;
  $seq_init(&((gcollator)->entries), 0, (void*)0);
  return gcollator;
}
/*@ depends_on \write(gcollator);
  @ assigns gcollator;
  @ reads \nothing;
  @*/
$atomic_f int $gcollator_destroy($gcollator gcollator)
{
  int numRemaining = (gcollator)->length;
  $free(gcollator);
  return numRemaining;
}
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$atomic_f $collator $collator_create($scope scope, $gcollator gcollator)
{
  $collator collator = ($collator)($malloc(scope, sizeof(struct _collator)));
  (collator)->gcollator = gcollator;
  return collator;
}
/*@ depends_on \write(collator);
  @ executes_when $true;
  @*/
$atomic_f void $collator_destroy($collator collator)
{
  $free(collator);
}
//======================== civlc.cvh =======================
$system[civlc] void $wait($proc p);
$system[civlc] void $waitall($proc* procs, int numProcs);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $exit(void);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] int $choose_int(int n);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $assert(_Bool expr, ...);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $assume(_Bool expr);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $elaborate(int x);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] int $next_time_count(void);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $pathCondition(void);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] _Bool $is_concrete_int(int value);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void* $malloc($scope s, int size);
/*@ depends_on \write(p);
  @ executes_when $true;
  @*/
$system[civlc] void $free(void* p);
/*@ depends_on \write(ptr);
  @ executes_when $true;
  @*/
$system[civlc] void $havoc(void* ptr);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] double $pow(double base, double exp);
//======================== string.h ========================
void* memcpy(void* p, void* q, size_t size);
void* memmove(void* dest, void* src, size_t n);
$system[string] void* memset(void* s, int c, size_t n);
int memcmp(void* s1, void* s2, size_t n);
void* memchr(void* s, int c, size_t n);
$system[string] char* strcpy(char* restrict s1, char* restrict s2);
char* strncpy(char* dest, char* src, size_t n);
char* strcat(char* dest, char* src);
char* strncat(char* dest, char* src, size_t n);
$system[string] int strcmp(char* s1, char* s2);
int strncmp(char* s1, char* s2, size_t n);
int strcoll(char* s1, char* s2);
size_t strxfrm(char* dest, char* src, size_t n);
char* strchr(char* s, int c);
char* strrchr(char* s, int c);
size_t strcspn(char* s, char* reject);
size_t strspn(char* s, char* accept);
char* strpbrk(char* s, char* accept);
char* strstr(char* s1, char* s2);
char* strtok(char* s, char* delim);
$system[string] size_t strlen(char* s);
char* strerror(int errnum);
//======================= bundle.cvh =======================
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[bundle] int $bundle_size($bundle b);
/*@ depends_on \write(ptr);
  @ executes_when $true;
  @*/
$system[bundle] $bundle $bundle_pack(void* ptr, int size);
/*@ depends_on \write(ptr);
  @ executes_when $true;
  @*/
$system[bundle] void $bundle_unpack($bundle bundle, void* ptr);
/*@ depends_on \write(buf);
  @ executes_when $true;
  @*/
$system[bundle] void $bundle_unpack_apply($bundle data, void* buf, int size, $operation op);
//======================= string.cvl =======================
void* memcpy(void* p, void* q, const size_t size)
{
  if (size == 0)
    return p;
  $bundle bundle = $bundle_pack(q, size);
  $bundle_unpack(bundle, p);
  return p;
}
//======================== civlc.cvh =======================
$system[civlc] void $wait($proc p);
$system[civlc] void $waitall($proc* procs, int numProcs);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $exit(void);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] int $choose_int(int n);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $assert(_Bool expr, ...);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $assume(_Bool expr);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $elaborate(int x);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] int $next_time_count(void);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $pathCondition(void);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] _Bool $is_concrete_int(int value);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void* $malloc($scope s, int size);
/*@ depends_on \write(p);
  @ executes_when $true;
  @*/
$system[civlc] void $free(void* p);
/*@ depends_on \write(ptr);
  @ executes_when $true;
  @*/
$system[civlc] void $havoc(void* ptr);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] double $pow(double base, double exp);
//======================== stdlib.h ========================
double atof(char* nptr);
int atoi(char* nptr);
long atol(char* nptr);
long long atoll(char* nptr);
double strtod(char* restrict nptr, char** restrict endptr);
float strtof(char* restrict nptr, char** restrict endptr);
long double strtold(char* restrict nptr, char** restrict endptr);
long strtol(char* restrict nptr, char** restrict endptr, int base);
long long strtoll(char* restrict nptr, char** restrict endptr, int base);
unsigned long strtoul(char* restrict nptr, char** restrict endptr, int base);
unsigned long long strtoull(char* restrict nptr, char** restrict endptr, int base);
$system[stdlib] int rand(void);
$system[stdlib] void srand(unsigned seed);
$system[stdlib] long random(void);
$system[stdlib] void srandom(unsigned seed);
void* aligned_alloc(size_t alignment, size_t size);
void* calloc(size_t nmemb, size_t size);
$system[stdlib] void free(void* ptr);
$system[stdlib] void* malloc(size_t size);
void* realloc(void* ptr, size_t size);
_Noreturn void abort(void);
int atexit( (void (void))* func);
int at_quick_exit( (void (void))* func);
$system[stdlib] void exit(int status);
_Noreturn void _Exit(int status);
char* getenv(char* name);
_Noreturn void quick_exit(int status);
int system(char* string);
void* bsearch(void* key, void* base, size_t nmemb, size_t size,  (int (void*, void*))* compar);
void qsort(void* base, size_t nmemb, size_t size,  (int (void*, void*))* compar);
int abs(int j);
long labs(long j);
long long llabs(long long j);
div_t div(int numer, int denom);
ldiv_t ldiv(long numer, long denom);
lldiv_t lldiv(long long numer, long long denom);
int mblen(char* s, size_t n);
int mbtowc(wchar_t* restrict pwc, char* restrict s, size_t n);
int wctomb(char* s, wchar_t wchar);
size_t mbstowcs(wchar_t* restrict pwcs, char* restrict s, size_t n);
size_t wcstombs(char* restrict s, wchar_t* restrict pwcs, size_t n);
constraint_handler_t set_constraint_handler_s(constraint_handler_t handler);
void abort_handler_s(char* restrict msg, void* restrict ptr, errno_t error);
void ignore_handler_s(char* restrict msg, void* restrict ptr, errno_t error);
errno_t getenv_s(size_t* restrict len, char* restrict value, rsize_t maxsize, char* restrict name);
void* bsearch_s(void* key, void* base, rsize_t nmemb, rsize_t size,  (int (void* k, void* y, void* context))* compar, void* context);
errno_t qsort_s(void* base, rsize_t nmemb, rsize_t size,  (int (void* x, void* y, void* context))* compar, void* context);
errno_t wctomb_s(int* restrict status, char* restrict s, rsize_t smax, wchar_t wc);
errno_t mbstowcs_s(size_t* restrict retval, wchar_t* restrict dst, rsize_t dstmax, char* restrict src, rsize_t len);
errno_t wcstombs_s(size_t* restrict retval, char* restrict dst, rsize_t dstmax, wchar_t* restrict src, rsize_t len);
//======================= stdlib.cvl =======================
int rand()
{
  int tmp;
  $havoc(&(tmp));
  return tmp;
}
void srand(unsigned seed)
{
}
void srandom(unsigned seed)
{
}
long random()
{
  long tmp;
  $havoc(&(tmp));
  return tmp;
}
void exit(int status)
{
  $assert(status == 0, "erroneous exit with code %d", status);
  $exit();
}
_Noreturn void abort(void)
{
  $exit();
}
int abs(int x)
{
  if (x >= 0)
    return x;
  return -x;
}
//======================== civlc.cvh =======================
$system[civlc] void $wait($proc p);
$system[civlc] void $waitall($proc* procs, int numProcs);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $exit(void);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] int $choose_int(int n);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $assert(_Bool expr, ...);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $assume(_Bool expr);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $elaborate(int x);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] int $next_time_count(void);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void $pathCondition(void);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] _Bool $is_concrete_int(int value);
/*@ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] void* $malloc($scope s, int size);
/*@ depends_on \write(p);
  @ executes_when $true;
  @*/
$system[civlc] void $free(void* p);
/*@ depends_on \write(ptr);
  @ executes_when $true;
  @*/
$system[civlc] void $havoc(void* ptr);
/*@ pure;
  @ depends_on \nothing;
  @ executes_when $true;
  @*/
$system[civlc] double $pow(double base, double exp);
//========================= seq.cvh ========================
/*@ depends_on \write(array);
  @ executes_when $true;
  @*/
$system[seq] int $seq_length(void* array);
/*@ depends_on \write(array, value);
  @ executes_when $true;
  @*/
$system[seq] void $seq_init(void* array, int count, void* value);
/*@ depends_on \write(array, values);
  @ executes_when $true;
  @*/
$system[seq] void $seq_insert(void* array, int index, void* values, int count);
/*@ depends_on \write(array, values);
  @ executes_when $true;
  @*/
$system[seq] void $seq_remove(void* array, int index, void* values, int count);
/*@ depends_on \write(array, values);
  @*/
$atomic_f void $seq_append(void* array, void* values, int count);
//========================= seq.cvl ========================
/*@ depends_on \write(array, values);
  @*/
$atomic_f void $seq_append(void* array, void* values, int count)
{
  int length = $seq_length(array);
  $seq_insert(array, length, values, count);
}
//=================== ContractTransformer ==================
int MPI_Comm_rank(MPI_Comm decl0, int* decl1);
int MPI_Comm_size(MPI_Comm decl0, int* decl1);
int MPI_Init(int* decl0, char*** decl1);
int MPI_Finalize();
$systemvoid $havoc(void* decl0);
$collate_state $mpi_snapshot(MPI_Comm decl0);
int $mpi_contract_enters(MPI_Comm decl0);
int $mpi_contract_entered(MPI_Comm decl0, $range decl1);
$system_Bool $collate_complete($collate_state decl0);
$system_Bool $collate_arrived($collate_state decl0, $range decl1);
//======================= allgather.c ======================
int broadcast(void* buf, int count, MPI_Datatype datatype, int root, MPI_Comm comm)
{
  int $mpi_comm_rank;
  int $mpi_comm_size;
  MPI_Comm_rank(comm, &($mpi_comm_rank));
  MPI_Comm_size(comm, &($mpi_comm_size));
  $collate_state _conc_cp0 = $mpi_snapshot(comm);
  $run
    $when ($collate_complete(_conc_cp0))
      $with(_conc_cp0)      {
        $assert(((0 < count) && (count <= 3)) && ($mpi_valid(buf, count, datatype) && (((0 <= root) && (root < $mpi_comm_size)) && ($mpi_agree(root) && $mpi_agree(count * $mpi_extent(datatype))))));
        if ($mpi_comm_rank != root)
          $assert();
        $assert($comm_empty_in(comm.p2p) && $comm_empty_out(comm.p2p));
      }
  int $result;
  $havoc(&($result));
  $collate_state _conc_pre_cp1 = $mpi_snapshot(comm);
  $with(_conc_pre_cp1)    $assume($mpi_equals(buf, count, datatype, \remote(buf , root)) && (\result == 0));
  $run
    if ($mpi_comm_rank != root)
      $when ($collate_arrived(_conc_pre_cp1, root))
        $with(_conc_pre_cp1)          $assume();
  return $result;
}
int gather(void* sendbuf, int sendcount, MPI_Datatype sendtype, void* recvbuf, int recvcount, MPI_Datatype recvtype, int root, MPI_Comm comm)
{
  int $mpi_comm_rank;
  int $mpi_comm_size;
  MPI_Comm_rank(comm, &($mpi_comm_rank));
  MPI_Comm_size(comm, &($mpi_comm_size));
  $collate_state _conc_cp2 = $mpi_snapshot(comm);
  $run
    $when ($collate_complete(_conc_cp2))
      $with(_conc_cp2)      {
        $assert(($mpi_agree(root) && $mpi_agree($mpi_extent(sendtype) * sendcount)) && (((sendcount > 0) && (sendcount < 3)) && (((recvcount > 0) && (recvcount < 3)) && (((0 <= root) && (root < $mpi_comm_size)) && $mpi_valid(sendbuf, sendcount, sendtype)))));
        if ($mpi_comm_rank == root)
          $assert($mpi_valid(recvbuf, recvcount * $mpi_comm_size, recvtype) && ((recvcount * $mpi_extent(recvtype)) == (sendcount * $mpi_extent(sendtype))));
        $assert($comm_empty_in(comm.p2p) && $comm_empty_out(comm.p2p));
      }
  int $result;
  $havoc(&($result));
  $collate_state _conc_pre_cp3 = $mpi_snapshot(comm);
  $run
    if ($mpi_comm_rank == root)
      $when ($collate_arrived(_conc_pre_cp3, 0 .. $mpi_comm_size - 1))
        $with(_conc_pre_cp3)          $assume($mpi_equals($mpi_offset(recvbuf, root * sendcount, sendtype), sendcount, sendtype, sendbuf) && $forall (int i | (i >= 0) && (i < $mpi_comm_size)) $mpi_equals($mpi_offset(recvbuf, i * sendcount, recvtype), sendcount, sendtype, \remote(sendbuf , i)));
  return $result;
}
int allgather(void* sendbuf, int sendcount, MPI_Datatype sendtype, void* recvbuf, int recvcount, MPI_Datatype recvtype, MPI_Comm comm)
{
  int place;
  int nprocs;
  $elaborate(recvcount);
  $elaborate(sendcount);
  MPI_Comm_rank(comm, &(place));
  MPI_Comm_size(comm, &(nprocs));
  gather(sendbuf, sendcount, sendtype, recvbuf, recvcount, recvtype, 0, comm);
  broadcast(recvbuf, recvcount * nprocs, recvtype, 0, comm);
  return 0;
}
//=================== ContractTransformer ==================
int _driver_allgather()
{
  void* sendbuf;
  $havoc(&(sendbuf));
  int sendcount;
  $havoc(&(sendcount));
  MPI_Datatype sendtype;
  $havoc(&(sendtype));
  void* recvbuf;
  $havoc(&(recvbuf));
  int recvcount;
  $havoc(&(recvcount));
  MPI_Datatype recvtype;
  $havoc(&(recvtype));
  MPI_Comm comm = MPI_COMM_WORLD;
  int $mpi_comm_rank;
  int $mpi_comm_size;
  MPI_Comm_rank(comm, &($mpi_comm_rank));
  MPI_Comm_size(comm, &($mpi_comm_size));
  $collate_state _conc_pre_cp4 = $mpi_snapshot(comm);
  $when ($collate_complete(_conc_pre_cp4))
    $with(_conc_pre_cp4)    {
      $assume($mpi_agree(sendcount * $mpi_extent(sendtype)) && (((sendcount >= 0) && (((sendcount * $mpi_extent(sendtype)) * $mpi_comm_size) < 3)) && (((recvcount >= 0) && (((recvcount * $mpi_extent(recvtype)) * $mpi_comm_size) < 3)) && ($mpi_valid(sendbuf, sendcount, sendtype) && ($mpi_valid(recvbuf, recvcount * $mpi_comm_size, recvtype) && (($mpi_extent(recvtype) * recvcount) == ($mpi_extent(sendtype) * sendcount)))))));
    }
  $mpi_contract_enters(comm);
  int $result = allgather(sendbuf, sendcount, sendtype, recvbuf, recvcount, recvtype, comm);
  $collate_state _conc_post_cp5 = $mpi_snapshot(comm);
  $when ($collate_complete(_conc_post_cp5))
    $with(_conc_post_cp5)    {
      $assert($mpi_agree($mpi_region(recvbuf, recvcount * $mpi_comm_size, recvtype)) && $mpi_equals(sendbuf, sendcount, sendtype, $mpi_offset(recvbuf, $mpi_comm_rank * recvcount, recvtype)));
      $assert($comm_empty_in(comm.p2p) && $comm_empty_out(comm.p2p));
    }
}
int main()
{
  MPI_Init((void*)0, (void*)0);
  _driver_allgather();
  MPI_Finalize();
}
