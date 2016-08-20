#include<mpi.h>
#include<civlc.cvh>
int left, right, nxl, nx, rank, nprocs;
double * u, * u_new, k;

#define OWNER(index) ((nprocs*(index+1)-1)/nx)

#define LOCAL_OF(index) [index - (OWNER(index)*nx/nprocs) + 1]

#define FIRST(rank) ((rank)*nx/nprocs)

#define READ(index)  (\on(OWNER(index), u)LOCAL_OF(index))

/*@ \mpi_collective(MPI_COMM_WORLD, P2P):
  @   requires rank == \mpi_comm_rank;
  @   requires nxl > 0 && nxl < 5;         //nxl shall not equal to zero
  @   requires \mpi_valid(u, nxl + 2, MPI_DOUBLE);
  @   behavior maxrank:
  @     assumes rank == \mpi_comm_size - 1;
  @     requires right == MPI_PROC_NULL && left == rank - 1;
  @     assigns  \mpi_region(u, 1, MPI_DOUBLE);
  @     ensures  \on(left, u[nxl]) == u[0];       
  @     waitsfor left;
  @   behavior minrank:
  @     assumes rank == 0;
  @     requires left == MPI_PROC_NULL && right == rank + 1;
  @     assigns  \mpi_region(&u[nxl+1], 1, MPI_DOUBLE);
  @     ensures  \on(right, u[1]) == u[nxl + 1];        
  @     waitsfor right;
  @   behavior others:
  @     assumes 0 < rank && rank < \mpi_comm_size - 1;
  @     requires left == rank - 1 && right == rank + 1;
  @     assigns  \mpi_region(u, 1, MPI_DOUBLE), 
  @              \mpi_region(&u[nxl+1], 1, MPI_DOUBLE);
  @     ensures  \on(left, u[nxl]) == u[0];             
  @     ensures  \on(right, u[1]) == u[nxl + 1];        
  @     waitsfor left, right;      
  @*/
void exchange_ghost_cells() {
  MPI_Sendrecv(&u[1], 1, MPI_DOUBLE, left, 0,
               &u[nxl+1], 1, MPI_DOUBLE, right, 0,
               MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  MPI_Sendrecv(&u[nxl], 1, MPI_DOUBLE, right, 0,
               &u[0], 1, MPI_DOUBLE, left, 0,
               MPI_COMM_WORLD, MPI_STATUS_IGNORE);
}

/*@ requires \valid(u + (0 .. (nxl + 1)));
  @ requires \valid(u_new + (0 .. (nxl + 1)));
  @ requires nxl > 0 && nxl <= 4;
  @ requires k > 0;
  @ assigns  u[1 .. (nxl + 1)];
  @ ensures  \forall int i; 0< i && i <= nxl
  @           ==> 
  @          u[i] == \old(u[i] + k*(u[i+1] + u[i-1] - 2*u[i]));
  @*/
void update() {
  for (int i = 1; i <= nxl; i++)
    u_new[i] = u[i] + k*(u[i+1] + u[i-1] - 2*u[i]);
  double * tmp = u_new; u_new=u; u=tmp;
}

/*@ 
  @ \mpi_collective(MPI_COMM_WORLD, P2P):
  @   requires rank == \mpi_comm_rank;
  @   requires nprocs == \mpi_comm_size;
  @   requires nxl > 0 && nxl < 5;
  @   requires nx > 5 && nx < 10;
  @   requires \mpi_valid(u, nxl + 2, MPI_DOUBLE);
  @   requires \mpi_valid(u_new, nxl + 2, MPI_DOUBLE);
  @   requires  nx == \sum(0, \mpi_comm_size - 1, 
  @                    (\lambda int k; \on(k, nxl)));
  @   requires k > 0.0;
  @   requires \mpi_agree(nx) && \mpi_agree(k);
  @   ensures  \forall int i; 1 <= i && i < nx - 1
  @            ==>
  @            READ(i) == 
  @            \old( 
  @               READ(i) + k* (READ(i+1) + READ(i-1) - 2*READ(i))
  @            ); 
  @   ensures  READ(nx - 1) == 
  @            \old( 
  @               READ(nx - 1) + k* (0 + READ(nx - 1 - 1) - 2*READ(nx - 1))
  @            ); 
  @   behavior maxrank:
  @     assumes rank == \mpi_comm_size - 1;
  @     requires right == MPI_PROC_NULL && left == rank - 1;
  @     requires u[nxl+1] == 0;
  @     requires nx - FIRST(\mpi_comm_rank) == nxl;
  @   behavior minrank:
  @     assumes rank == 0;
  @     requires left == MPI_PROC_NULL && right == 1;
  @     requires u[0] == 0;
  @     requires FIRST(\mpi_comm_rank+1) == nxl;
  @   behavior others:
  @     assumes 0 < rank && rank < \mpi_comm_size - 1;
  @     requires left == rank - 1 && right == rank + 1;
  @     requires nxl == FIRST(\mpi_comm_rank + 1) - FIRST(\mpi_comm_rank);
  @*/
void diff1dIter() {
  $elaborate(nxl);
  exchange_ghost_cells();
  update();
}
