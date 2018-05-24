#include <string.h>
#include "allreduce.h"

GS_DEFINE_DOM_SIZES()

#define DEFINE_PROCS(T) \
  GS_FOR_EACH_OP(T,DEFINE_GATHER) 

GS_FOR_EACH_DOMAIN(DEFINE_PROCS)

#undef DEFINE_PROCS

void gs_gather_array(void *out, const void *in, uint n, gs_dom dom, gs_op op)
{
#define WITH_OP(T,OP) gather_array_##T##_##OP(out,in,n)
#define WITH_DOMAIN(T) SWITCH_OP(T,op)
  SWITCH_DOMAIN(dom);
#undef  WITH_DOMAIN
#undef  WITH_OP
}

static void comm_send(const struct comm *c, void *p, size_t n,
                      uint dst, int tag)
{
  MPI_Send(p,n,MPI_UNSIGNED_CHAR,dst,tag,c->c);
}

static void comm_recv(const struct comm *c, void *p, size_t n,
                      uint src, int tag)
{
  MPI_Recv(p,n,MPI_UNSIGNED_CHAR,src,tag,c->c,MPI_STATUS_IGNORE);
}

static void allreduce_imp(const struct comm *com, gs_dom dom, gs_op op,
                          void *v, uint vn, void *buf)
{
  size_t total_size = vn*gs_dom_size[dom];
  const uint id=com->id, np=com->np;
  uint n = np, c=1, odd=0, base=0;
  while(n>1) {
    odd=(odd<<1)|(n&1);
    c<<=1, n>>=1;
    if(id>=base+n) c|=1, base+=n, n+=(odd&1);
  }
  while(n<np) {
    if(c&1) n-=(odd&1), base-=n;
    c>>=1, n<<=1, n+=(odd&1);
    odd>>=1;
    if(base==id) {
      comm_recv(com, buf,total_size, id+n/2,id+n/2);
      gs_gather_array(v,buf,vn, dom,op);
    } else {
      comm_send(com, v,total_size, base,id);
      break;
    }
  }
  while(n>1) {
    if(base==id)
      comm_send(com, v,total_size, id+n/2,id);
    else
      comm_recv(com, v,total_size, base,base);
    odd=(odd<<1)|(n&1);
    c<<=1, n>>=1;
    if(id>=base+n) c|=1, base+=n, n+=(odd&1);
  }
}

void comm_allreduce(const struct comm *com, gs_dom dom, gs_op op,
                          void *v, uint vn, void *buf)
{
  if(vn==0) return;
  MPI_Datatype mpitype;
  MPI_Op mpiop;
#define DOMAIN_SWITCH() do {					     \
    switch(dom) { case gs_double:    mpitype=MPI_DOUBLE;    break;   \
      case gs_float:     mpitype=MPI_FLOAT;     break;		     \
      case gs_int:       mpitype=MPI_INT;       break;		     \
      case gs_long:      mpitype=MPI_LONG;      break;               \
      default:        goto comm_allreduce_byhand;				\
      }  									\
} while(0)

    DOMAIN_SWITCH();
    #undef DOMAIN_SWITCH
    switch(op) { case gs_add: mpiop=MPI_SUM;  break;
                 case gs_mul: mpiop=MPI_PROD; break;
                 case gs_min: mpiop=MPI_MIN;  break;
                 case gs_max: mpiop=MPI_MAX;  break;
                 default:        goto comm_allreduce_byhand;
    }
    MPI_Allreduce(v,buf,vn,mpitype,mpiop,com->c);
    memcpy(v,buf,vn*gs_dom_size[dom]);
    return;

 comm_allreduce_byhand:
  allreduce_imp(com,dom,op, v,vn, buf);
}
