#include<mpi.h>
int left, right, nxl, nx, rank, nsteps;
double * u, * u_new;

/*@ \mpi_collective[MPI_COMM_WORLD, P2P]:
  @   requires rank == \mpi_comm_rank;
  @   requires nxl > 0;
  @   requires \mpi_valid(u, MPI_DOUBLE, nxl + 2);
  @   ensures  \remote(u[nxl + 1], left) == u[1];         //deliver 1
  @   ensures  \remote(u[0], right) == u[nxl];            //deliver 2
  @   ensures  \remote(u[nxl], left) == u[0];             //obtain  1
  @   ensures  \remote(u[1], right) == u[nxl + 1];        //obtain  2
  @   behavior maxrank:
  @     assume rank == \mpi_comm_size - 1;
  @     requires right == 0 && left == rank - 1;
  @   behavior minrank:
  @     assume rank == 0;
  @     requires left == \mpi_comm_size - 1 && right == rank + 1;
  @   behavior others:
  @     assume 0 < rank && rank < \mpi_comm_size;
  @     requires left == rank - 1 && right == rank + 1;
  @*/
void exchange_ghost_cells() {
  MPI_Sendrecv(&u[1], 1, MPI_DOUBLE, left, 0,
               &u[nxl+1], 1, MPI_DOUBLE, right, 0,
               MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  MPI_Sendrecv(&u[nxl], 1, MPI_DOUBLE, right, 0,
               &u[0], 1, MPI_DOUBLE, left, 0,
               MPI_COMM_WORLD, MPI_STATUS_IGNORE);
}

/*@ requires \valid(u + (0 .. (nxl + 2)));
  @ requires \valid(u_new + (0 .. (nxl + 2)));
  @ requires nxl > 0;
  @ requires k > 0;
  @ assigns  u_new[0 .. (nxl + 2)];
  @ ensures  \forall int i; 0< i <= nxl
  @           ==> 
  @          u[i] == \old(u[i] + k*(u[i+1] + u[i-1] - 2*u[i]));
  @*/
void update() {
  /*@
    @ loop invariants \forall int j; 0< j < i
    @                  ==> 
    @                 u_new[j] == u[j] + k*(u[j+1] + u[j-1] - 2*u[j]);
    @*/
  for (int i = 1; i <= nxl; i++)
    u_new[i] = u[i] + k*(u[i+1] + u[i-1] - 2*u[i]);
  double * tmp = u_new; u_new=u; u=tmp;
}

/*@ requires nsteps > 1;
  @ \mpi_collective[MPI_COMM_WORLD, P2P]:
  @   requires rank == \mpi_comm_rank;
  @   requires nxl > 0;
  @   requires \mpi_valid(u, MPI_DOUBLE, nxl + 2);
  @   requires \mpi_valid(u_new, MPI_DOUBLE, nxl + 2);
  @   requires  nx == \sum(0, \mpi_comm_size - 1, 
  @                    (\lambda int k; \remote(nxl, k)));
  @   ensures  \forall int i; 0 < i <= nx
  @             ==>
  @            u[i] == \old(u[i] + k*(u[i+1] + u[i-1] - 2*u[i]));
  @   behavior maxrank:
  @     assume rank == \mpi_comm_size - 1;
  @     requires right == 0 && left == rank - 1;
  @   behavior minrank:
  @     assume rank == 0;
  @     requires left == \mpi_comm_size - 1 && right == rank + 1;
  @   behavior others:
  @     assume 0 < rank && rank < \mpi_comm_size;
  @     requires left == rank - 1 && right == rank + 1;
  @*/
void diff1dIter() {
    exchange_ghost_cells();
    update();
}
