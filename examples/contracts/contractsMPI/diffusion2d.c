double ** u_curr, ** u_next;
int nxl, nyl, nx, ny;
int rank, nprocsx, nprocsy;

/*@ requires \valid(u_curr + (0 .. (nyl + 2)));
  @ requires \valid(u_next + (0 .. (nyl + 2)));
  @ requires \valid(u_curr[0 .. (nyl+2)] + (0 .. (nxl + 2)));
  @ requires \valid(u_next[0 .. (nyl+2)] + (0 .. (nxl + 2)));
  @ requires nxl > 0 && nyl > 0 && k > 0;
  @ ensures  \forall int i, j; 1 <= i <= nyl && 
  @                            1 <= j <= nxl ==>
  @          u_curr[i][j] == \old(u_curr[i][j] +
  @          k*(u_curr[i+1][j] + u_curr[i-1][j] + 
  @          u_curr[i][j+1] + u_curr[i][j-1] - 4*u_curr[i][j]));
  @
  @*/
void update() {
  double **tmp;

  /*@ loop invariants \forall int k, m; 1<= k < i && 1 <=m <= nxl ==>
    @                  u_next[k][m] == u_curr[k][m] +
    @                  k*(u_curr[k+1][m] + u_curr[k-1][m] + 
    @                  u_curr[k][m+1] + u_curr[k][m-1] - 4*u_curr[k][m]);
   */
  for (int i = 1; i < nyl + 1; i++)
    /*@ loop invariants \forall int k; 1 <= k < j ==>
      @                  u_next[i][k] = u_curr[i][k] +
      @                  k*(u_curr[i+1][k] + u_curr[i-1][k] + 
      @                  u_curr[i][k+1] + u_curr[i][k-1] - 4*u_curr[i][k]);
      @*/
    for (int j = 1; j < nxl + 1; j++) {
      u_next[i][j] = u_curr[i][j] +
        k*(u_curr[i+1][j] + u_curr[i-1][j] + 
           u_curr[i][j+1] + u_curr[i][j-1] - 4*u_curr[i][j]);
    }
  // swap two pointers
  tmp = u_curr;
  u_curr = u_next;
  u_next = tmp;
}

/* The processes are arranged geometrically as follows for the case
 * NPROCSX = 3:
 * row 0: 0 1 2
 * row 1: 3 4 5 
 * ...         
 */

/*@ \mpi_collective[MPI_COMM_WORLD, P2P]:
  @   requires \mpi_valid(u_curr[1], MPI_DOUBLE, 0);
  @             && \mpi_valid(u_curr[nyl], MPI_DOUBLE, 0);
  @             && \mpi_valid(u_next[1], MPI_DOUBLE, 0);
  @             && \mpi_valid(u_next[nyl], MPI_DOUBLE, 0);
  @   requires \mpi_valid(&u_curr[1][1], MPI_DOUBLE, nxl);
  @   requires \mpi_valid(&u_curr[nyl][1], MPI_DOUBLE, nxl);
  @   requires \mpi_valid(&u_next[1][1], MPI_DOUBLE, nxl);
  @   requires \mpi_valid(&u_next[nyl][1], MPI_DOUBLE, nxl);
  @   requires rank == \mpi_comm_rank;
  @   requires nprocsx * nprocsy == \mpi_comm_size;
  @   ensures  top != MPI_PROC_NULL ==> 
  @            \mpi_equals(&u_curr[1][1], MPI_DOUBLE, nxl, \remote(&u_curr[nyl+1][1], top));  // obtain
  @   ensures  bottom != MPI_PROC_NULL ==> 
  @            \mpi_equals(&u_curr[nyl][1], MPI_DOUBLE, nxl, \remote(&u_curr[0][1], bottom)); // obtain
  @   ensures  left != MPI_PROC_NULL ==> (\forall int i; 1 <= i <= nyl
  @                                       ==>
  @                                       u_curr[i][1] == \remote(u_curr[i][nxl+1], left);    // obtain
  @   ensures  right != MPI_PROC_NULL ==> (\forall int i; 1 <= i <= nyl
  @                                       ==>
  @                                       u_curr[i][nxl] == \remote(u_curr[i][0], right);     // obtain
  @   waitsfor top, bottom, left, right;
  @   behavior rightmost
  @     assume (rank + 1) % nprocsx == 0;
  @     requires left == MPI_PROC_NULL;
  @   behavior leftmost
  @     assume rank % nprocsx == 0;
  @     requires right = MPI_PROC_NULL;
  @   behavior atButton
  @     assume nprocsx * nprocsy - nprocsx <= rank
  @            && rank < nprocsx * nprocsy;
  @	requires button == MPI_PROC_NULL;
  @   behavior atTop
  @     assume 0<= rank && rank < nprocsx;
  @     requires top == MPI_PROC_NULL;
  @   behavior others
  @     assume nprocsx <= rank && rank < (nprocsx * nprocsy - nprocsx)
  @            && (rank + 1) % nprocs x != 0 && rank % nprocsx != 0;
  @     requires right == rank + 1 && left == rank - 1
  @              && top == rank - nprocsx && button == rank + nprocsx;
  @*/
void exchange() {
  double sendbuf[nyl];
  double recvbuf[nyl];

  // sends top border row, receives into bottom ghost cell row
  MPI_Sendrecv(&u_curr[1][1], nxl, MPI_DOUBLE, top, FROMBOTTOM, &u_curr[nyl+1][1], nxl, 
               MPI_DOUBLE, bottom, FROMBOTTOM, comm, MPI_STATUS_IGNORE);
  // sends bottom border row, receives into top ghost cell row
  MPI_Sendrecv(&u_curr[nyl][1], nxl, MPI_DOUBLE, bottom, FROMTOP, &u_curr[0][1], nxl, 
               MPI_DOUBLE, top, FROMTOP, comm, MPI_STATUS_IGNORE);
  // sends left border column, receives into temporary buffer
  for (int i = 0; i < nyl; i++) sendbuf[i] = u_curr[i+1][1];
  MPI_Sendrecv(sendbuf, nyl, MPI_DOUBLE, left, FROMRIGHT, recvbuf, nyl, 
               MPI_DOUBLE, right, FROMRIGHT, comm, MPI_STATUS_IGNORE);
  // copies temporary buffer into right ghost cell column
  if (right != MPI_PROC_NULL)
    for (int i = 0; i < nyl; i++) u_curr[i+1][nxl+1] = recvbuf[i];
  // sends right border column, receives into temporary buffer
  for (int i = 0; i < nyl; i++) sendbuf[i] = u_curr[i+1][nxl];
  MPI_Sendrecv(sendbuf, nyl, MPI_DOUBLE, right, FROMLEFT, recvbuf, nyl, 
               MPI_DOUBLE, left, FROMLEFT, comm, MPI_STATUS_IGNORE);
  // copies temporary buffer into left ghost cell column
  if (left != MPI_PROC_NULL)
    for (int i = 0; i < nyl; i++) u_curr[i+1][0] = recvbuf[i];
}

/*@ requires nx > 0 && ny > 0 && nyl > 0 && nxl > 0;
  @ \mpi_collective[MPI_COMM_WORLD, P2P]:
  @   requires \mpi_valid(u_curr[1], MPI_DOUBLE, 0);
  @             && \mpi_valid(u_curr[nyl], MPI_DOUBLE, 0);
  @             && \mpi_valid(u_next[1], MPI_DOUBLE, 0);
  @             && \mpi_valid(u_next[nyl], MPI_DOUBLE, 0);
  @   requires \mpi_valid(&u_curr[1][1], MPI_DOUBLE, nxl);
  @   requires \mpi_valid(&u_curr[nyl][1], MPI_DOUBLE, nxl);
  @   requires \mpi_valid(&u_next[1][1], MPI_DOUBLE, nxl);
  @   requires \mpi_valid(&u_next[nyl][1], MPI_DOUBLE, nxl);
  @   requires rank == \mpi_comm_rank;
  @   requires nprocsx * nprocsy == \mpi_comm_size;
  @   requires nx == \sum(0, \mpi_comm_size - 1, (\lambda int k; \remote(nxl, k)));
  @   requires ny == \sum(0, \mpi_comm_size - 1, (\lambda int k; \remote(nyl, k)));
  @   ensures  \forall int i, j; 0 <= i < ny && 
  @                            0 <= j < nx ==>
  @          u_curr[i][j] == \old(u_curr[i][j] +
  @          k*(u_curr[i+1][j] + u_curr[i-1][j] + 
  @          u_curr[i][j+1] + u_curr[i][j-1] - 4*u_curr[i][j]));
  @   behavior rightmost
  @     assume (rank + 1) % nprocsx == 0;
  @     requires left == MPI_PROC_NULL;
  @   behavior leftmost
  @     assume rank % nprocsx == 0;
  @     requires right = MPI_PROC_NULL;
  @   behavior atButton
  @     assume nprocsx * nprocsy - nprocsx <= rank
  @            && rank < nprocsx * nprocsy;
  @	requires button == MPI_PROC_NULL;
  @   behavior atTop
  @     assume 0<= rank && rank < nprocsx;
  @     requires top == MPI_PROC_NULL;
  @   behavior others
  @     assume nprocsx <= rank && rank < (nprocsx * nprocsy - nprocsx)
  @            && (rank + 1) % nprocs x != 0 && rank % nprocsx != 0;
  @     requires right == rank + 1 && left == rank - 1
  @              && top == rank - nprocsx && button == rank + nprocsx;
  @*/
void diff2dIter() {
  exchange_ghost_cells();
  update();
}
