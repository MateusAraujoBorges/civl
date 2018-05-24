/* FEVS: A Functional Equivalence Verification Suite for High-Performance
 * Scientific Computing
 *
 * Copyright (C) 2010, Stephen F. Siegel, Timothy K. Zirkel,
 * University of Delaware
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA.
 */

#include<stdio.h>
#include<stdlib.h>
#include"mpi.h"
#include<civlc.cvh>

#pragma CIVL ACSL

$input int N;
$assume(N > 0);
$input double a[N];
$output double __sum;

double sum;
double localSum = 0.0;
int PID;
int NPROCS;
    
int main(int argc, char *argv[]) {
  int n, first, afterLast, i;

  MPI_Init(&argc, &argv);
  MPI_Comm_size(MPI_COMM_WORLD, &NPROCS);
  MPI_Comm_rank(MPI_COMM_WORLD, &PID);
  n = N;
  first = n*PID/NPROCS;
  afterLast = n*(PID+1)/NPROCS;
  
  /*@ loop invariant first <= i <= afterLast;
    @ loop invariant localSum == \sum(first, i-1, \lambda int t; a[t]);
    @ loop assigns localSum, i;
    @*/
  for (i=first; i<afterLast; i++) 
    localSum += a[i];
  
  MPI_Reduce(&localSum, &sum, 1, MPI_DOUBLE, MPI_SUM, 0, MPI_COMM_WORLD);
  if (PID == 0)
    __sum = sum;
  MPI_Finalize();
  return 0;
}


