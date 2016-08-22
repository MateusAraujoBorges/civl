#include <mpi.h>
#define FROMLEFT   0
#define FROMRIGHT  1
#define FROMBOTTOM 2
#define FROMTOP    3
#define comm MPI_COMM_WORLD

double (*u)[];
double (*u_new)[];
double k;
int nxl, nyl, nx, ny;
int rank, nprocsx, nprocsy, left, right, top, bottom;

/*@ requires \valid((double (*)[nxl+2])u + (0 .. (nyl + 1)));
  @ requires \valid(((double (*)[nxl+2])u_new) + (0 .. (nyl + 1)));
  @ requires k > 0;
  @ requires 0 <= nxl && nxl < 5;
  @ requires 0 <= nyl && nyl < 5;
  @ assigns  u[1 .. nyl][1 .. nxl];
  @ ensures  \forall int i, j; 1 <= i <= nyl && 
  @                            1 <= j <= nxl ==>
  @          u[i][j] == \old(u[i][j] +
  @          k*(u[i+1][j] + u[i-1][j] + 
  @          u[i][j+1] + u[i][j-1] - 4*u[i][j]));
  @*/
void update() {
  double (* tmp)[];

  for (int i = 1; i < nyl + 1; i++)
    for (int j = 1; j < nxl + 1; j++) {
      u_new[i][j] = u[i][j] +
        k*(u[i+1][j] + u[i-1][j] + 
           u[i][j+1] + u[i][j-1] - 4*u[i][j]);
    }
  tmp = u;
  u = u_new;
  u_new = tmp;
}

/* The processes are arranged geometrically as follows for the case
 * NPROCSX = 3:
 * row 0: 0 1 2
 * row 1: 3 4 5 
 * ...         
 */

/*@ requires \valid((double (*)[nxl+2])u + (0 .. (nyl + 1)));
  @ requires \valid((double (*)[nxl+2])u_new + (0 .. (nyl + 1)));
  @ \mpi_collective(MPI_COMM_WORLD, P2P):
  @   requires rank == \mpi_comm_rank;
  @   requires nprocsx * nprocsy == \mpi_comm_size && nprocsx > 0 
  @            && nprocsy > 0;
  @   requires (rank + 1) % nprocsx == 0 ==> right == MPI_PROC_NULL &&
  @            !((rank + 1) % nprocsx == 0) ==> right == rank + 1;
  @   requires rank % nprocsx == 0 ==> left == MPI_PROC_NULL &&
  @            !(rank % nprocsx == 0) ==> left == rank - 1;
  @   requires nprocsx * nprocsy - nprocsx <= rank && rank < nprocsx * nprocsy
  @            ==> bottom == MPI_PROC_NULL  &&
  @            !(nprocsx * nprocsy - nprocsx <= rank && rank < nprocsx * nprocsy)
  @            ==> bottom == rank + nprocsx;
  @   requires 0<= rank && rank < nprocsx ==> top == MPI_PROC_NULL &&
  @            !(0<= rank && rank < nprocsx) ==> top == rank - nprocsx;
  @   ensures  top != MPI_PROC_NULL ==> 
  @            \mpi_equals(&u[0][1], nxl, MPI_DOUBLE, \on(top, &u[nyl][1])); 
  @   ensures  bottom != MPI_PROC_NULL ==> 
  @            \mpi_equals(&u[nyl+1][1], nxl, MPI_DOUBLE, \on(bottom, &u[1][1])); 
  @   ensures  left != MPI_PROC_NULL ==> (\forall int i; 1 <= i <= nyl  ==>
  @                                       u[i][0] == \on(left, u[i][nxl])); 
  @   ensures  right != MPI_PROC_NULL ==> (\forall int i; 1 <= i <= nyl ==>
  @                                       u[i][nxl+1] == \on(right, u[i][1])); 
  @   waitsfor bottom, top, right, left;
  @   behavior assign_by_left:
  @     assumes rank % nprocsx != 0;
  @     assigns u[1 .. nyl][0];
  @   behavior assign_by_right:
  @     assumes (rank + 1) % nprocsx != 0;
  @     assigns u[1 .. nyl][nxl+1];
  @   behavior assign_by_top:
  @     assumes !(0 <= rank && rank < nprocsx);
  @     assigns u[0][1 .. nxl];
  @   behavior assign_by_bottom:
  @     assumes !(nprocsx * nprocsy - nprocsx <= rank && rank < nprocsx * nprocsy);
  @     assigns u[nyl+1][1 .. nxl];
  @*/
void exchange() {
  double sendbuf[nyl];
  double recvbuf[nyl];

  // sends top border row, receives into bottom ghost cell row
  MPI_Sendrecv(&u[1][1], nxl, MPI_DOUBLE, top, FROMBOTTOM, &u[nyl+1][1], nxl, 
               MPI_DOUBLE, bottom, FROMBOTTOM, comm, MPI_STATUS_IGNORE);
  // sends bottom border row, receives into top ghost cell row
  MPI_Sendrecv(&u[nyl][1], nxl, MPI_DOUBLE, bottom, FROMTOP, &u[0][1], nxl, 
               MPI_DOUBLE, top, FROMTOP, comm, MPI_STATUS_IGNORE);
  // sends left border column, receives into temporary buffer
  for (int i = 0; i < nyl; i++) sendbuf[i] = u[i+1][1];
  MPI_Sendrecv(sendbuf, nyl, MPI_DOUBLE, left, FROMRIGHT, recvbuf, nyl, 
               MPI_DOUBLE, right, FROMRIGHT, comm, MPI_STATUS_IGNORE);
  // copies temporary buffer into right ghost cell column
  if (right != MPI_PROC_NULL)
    for (int i = 0; i < nyl; i++) u[i+1][nxl+1] = recvbuf[i];
  // sends right border column, receives into temporary buffer
  for (int i = 0; i < nyl; i++) sendbuf[i] = u[i+1][nxl];
  MPI_Sendrecv(sendbuf, nyl, MPI_DOUBLE, right, FROMLEFT, recvbuf, nyl, 
               MPI_DOUBLE, left, FROMLEFT, comm, MPI_STATUS_IGNORE);
  // copies temporary buffer into left ghost cell column
  if (left != MPI_PROC_NULL)
    for (int i = 0; i < nyl; i++) u[i+1][0] = recvbuf[i];
}

