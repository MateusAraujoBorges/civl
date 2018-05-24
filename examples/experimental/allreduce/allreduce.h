#ifndef _ALLREDUCE_H_
#define _ALLREDUCE_H_

#include <mpi.h>

#define uint int

/****** carved out from comm ******/

typedef MPI_Comm comm_ext;
typedef MPI_Request comm_req;

struct comm {
  uint id, np;
  comm_ext c;
};

/****** carved out from gs_defs  ******/

/* the supported domains */
#define GS_FOR_EACH_DOMAIN(macro) \
  macro(double) \
  macro(float ) \
  macro(int   ) \
  macro(long  ) 
  //  WHEN_LONG_LONG(macro(long_long))
  
/* the supported ops */
#define GS_FOR_EACH_OP(T,macro) \
  macro(T,add) \
  macro(T,mul) \
  macro(T,min) \
  macro(T,max) \
  macro(T,bpr)

#define GS_DO_add(a,b) a+=b
#define GS_DO_mul(a,b) a*=b
#define GS_DO_min(a,b) if(b<a) a=b
#define GS_DO_max(a,b) if(b>a) a=b
#define GS_DO_bpr(a,b) \
  do if(b!=0) { uint a_ = a; uint b_ = b; \
       if(a_==0) { a=b_; break; } \
       for(;;) { if(a_<b_) b_>>=1; else if(b_<a_) a_>>=1; else break; } \
       a = a_; \
     } while(0)

/*------------------------------------------------------------------------------
  Enums and constants
------------------------------------------------------------------------------*/

/* domain enum */
#define LIST GS_FOR_EACH_DOMAIN(ITEM) gs_dom_n
#define ITEM(T) gs_##T,
typedef enum { LIST } gs_dom;
#undef ITEM
#undef LIST

/* domain type size array */
#define GS_DOM_SIZE_ITEM(T) sizeof(T),
#define GS_DEFINE_DOM_SIZES() \
  static const unsigned gs_dom_size[] = \
    { GS_FOR_EACH_DOMAIN(GS_DOM_SIZE_ITEM) 0 };

/* operation enum */
#define LIST GS_FOR_EACH_OP(T,ITEM) gs_op_n
#define ITEM(T,op) gs_##op,
typedef enum { LIST } gs_op;
#undef ITEM
#undef LIST

/****** carved out from gs_local  ******/

#define SWITCH_DOMAIN_CASE(T) case gs_##T: WITH_DOMAIN(T); break;
#define SWITCH_DOMAIN(dom) do switch(dom) { \
    GS_FOR_EACH_DOMAIN(SWITCH_DOMAIN_CASE) case gs_dom_n: break; } while(0)

#define SWITCH_OP_CASE(T,OP) case gs_##OP: WITH_OP(T,OP); break;
#define SWITCH_OP(T,op) do switch(op) { \
    GS_FOR_EACH_OP(T,SWITCH_OP_CASE) case gs_op_n: break; } while(0)

#define DEFINE_GATHER(T,OP) \
static void gather_array_##T##_##OP( \
  T *restrict out, const T *restrict in, uint n) \
{                                                                \
  for(;n;--n) { T q = *in++, *p = out++; GS_DO_##OP(*p,q); }      \
}

void gs_gather_array(void *out, const void *in, uint n, gs_dom dom, gs_op op);

/************ MPI API *************/
void comm_allreduce(const struct comm *com, gs_dom dom, gs_op op,
		    void *v, uint vn, void *buf);

#endif
