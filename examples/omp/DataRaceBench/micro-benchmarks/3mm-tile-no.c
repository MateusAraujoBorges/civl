/**
 * 3mm.c: This file is part of the PolyBench/C 3.2 test suite.
 * with tiling 16x16 and nested SIMD 
 *
 * Contact: Louis-Noel Pouchet <pouchet@cse.ohio-state.edu>
 * Web address: http://polybench.sourceforge.net
 */
#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <math.h>
/* Include polybench common header. */
#include <polybench.h>
/* Include benchmark-specific header. */
/* Default data type is double, default size is 4000. */
#include "3mm.h"
/* Array initialization. */

static void init_array(int ni,int nj,int nk,int nl,int nm,double A[128 + 0][128 + 0],double B[128 + 0][128 + 0],double C[128 + 0][128 + 0],double D[128 + 0][128 + 0])
{
  int i;
  int j;
{
    int c3;
    int c4;
    int c1;
    int c2;
    if (ni >= ((0 > -1 * nj + -1 * nm + 1?0 : -1 * nj + -1 * nm + 1)) && nj >= 0 && nk >= ((0 > -1 * nm + 1?0 : -1 * nm + 1)) && nm >= 0) {
#pragma omp parallel for private(c2, c4, c3)
      for (c1 = 0; c1 <= (((((nk + ni + nj + nm + -1) * 16 < 0?((16 < 0?-((-(nk + ni + nj + nm + -1) + 16 + 1) / 16) : -((-(nk + ni + nj + nm + -1) + 16 - 1) / 16))) : (nk + ni + nj + nm + -1) / 16)) < (((nk + ni + nj + 2 * nm + -2) * 16 < 0?((16 < 0?-((-(nk + ni + nj + 2 * nm + -2) + 16 + 1) / 16) : -((-(nk + ni + nj + 2 * nm + -2) + 16 - 1) / 16))) : (nk + ni + nj + 2 * nm + -2) / 16))?(((nk + ni + nj + nm + -1) * 16 < 0?((16 < 0?-((-(nk + ni + nj + nm + -1) + 16 + 1) / 16) : -((-(nk + ni + nj + nm + -1) + 16 - 1) / 16))) : (nk + ni + nj + nm + -1) / 16)) : (((nk + ni + nj + 2 * nm + -2) * 16 < 0?((16 < 0?-((-(nk + ni + nj + 2 * nm + -2) + 16 + 1) / 16) : -((-(nk + ni + nj + 2 * nm + -2) + 16 - 1) / 16))) : (nk + ni + nj + 2 * nm + -2) / 16)))); c1++) {
        if (c1 <= (((((((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)))) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)))) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)))) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)))) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))))) {
          for (c2 = 0; c2 <= (((((((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nj + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nj + -1)) < nk + -1?((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nj + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nj + -1)) : nk + -1)) < nm + -1?((((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nj + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nj + -1)) < nk + -1?((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nj + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nj + -1)) : nk + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nk + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nk + -1)) < nl + -1?((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nk + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nk + -1)) : nl + -1)) < nm + -1?((((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nk + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nk + -1)) < nl + -1?((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nk + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nk + -1)) : nl + -1)) : nm + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nk + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nk + -1)) < nm + -1?((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nk + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nk + -1)) : nm + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nk + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nk + -1)) < nl + -1?((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nk + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nk + -1)) : nl + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nl > nm?nl : nm); c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nk + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= ((((((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) < nl + -1?((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) : nl + -1)) < nm + -1?((((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) < nl + -1?((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) : nl + -1)) : nm + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nj > nl?nj : nl); c4 <= ((((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) < nm + -1?((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) : nm + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nj > nm?nj : nm); c4 <= ((((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) < nl + -1?((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) : nl + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (((nj > nl?nj : nl)) > nm?((nj > nl?nj : nl)) : nm); c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nk; c4 <= ((((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)) < nm + -1?((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)) : nm + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nk > nl?nk : nl); c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nm + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nm + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nk > nm?nk : nm); c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (((nk > nl?nk : nl)) > nm?((nk > nl?nk : nl)) : nm); c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nj > nk?nj : nk); c4 <= ((((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) < nm + -1?((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (((nj > nk?nj : nk)) > nl?((nj > nk?nj : nk)) : nl); c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (((nj > nk?nj : nk)) > nm?((nj > nk?nj : nk)) : nm); c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = nm; c3 <= ((((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nj + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nj + -1)) < nk + -1?((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nj + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nj + -1)) : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
              if (c1 == c2) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c4 = nm; c4 <= ((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nk + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nk + -1)); c4++) {
                  A[c3][c4] = ((double )c3) * c4 / ni;
                  B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                }
              }
              if (c1 == c2) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c4 = nj; c4 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c4++) {
                  A[c3][c4] = ((double )c3) * c4 / ni;
                }
              }
              if (c1 == c2) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c4 = nk; c4 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c4++) {
                  B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                }
              }
            }
            for (c3 = nj; c3 <= ((((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nk + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nk + -1)) < nm + -1?((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nk + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nk + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
              if (c1 == c2) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c4 = nj; c4 <= ((((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)) < nl + -1?((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)) : nl + -1)); c4++) {
                  A[c3][c4] = ((double )c3) * c4 / ni;
                  D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
                }
              }
              if (c1 == c2) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c4 = (nj > nl?nj : nl); c4 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c4++) {
                  A[c3][c4] = ((double )c3) * c4 / ni;
                }
              }
              if (c1 == c2) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c4 = nk; c4 <= ((16 * c1 + 15 < nl + -1?16 * c1 + 15 : nl + -1)); c4++) {
                  D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
                }
              }
            }
            for (c3 = (nj > nm?nj : nm); c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nk + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
              if (c1 == c2) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c4 = nj; c4 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c4++) {
                  A[c3][c4] = ((double )c3) * c4 / ni;
                }
              }
            }
            for (c3 = nk; c3 <= ((((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nj + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nj + -1)) < nm + -1?((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nj + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nj + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) < nl + -1?((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) : nl + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
              if (c1 == c2) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c4 = nk; c4 <= ((((16 * c1 + 15 < nl + -1?16 * c1 + 15 : nl + -1)) < nm + -1?((16 * c1 + 15 < nl + -1?16 * c1 + 15 : nl + -1)) : nm + -1)); c4++) {
                  C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                  D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
                }
              }
              if (c1 == c2) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c4 = (nk > nl?nk : nl); c4 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c4++) {
                  C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                }
              }
              if (c1 == c2) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c4 = nm; c4 <= ((16 * c1 + 15 < nl + -1?16 * c1 + 15 : nl + -1)); c4++) {
                  D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
                }
              }
            }
            for (c3 = (nk > nm?nk : nm); c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nj + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) < nm + -1?((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) : nm + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
              if (c1 == c2) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c4 = nm; c4 <= nk + -1; c4++) {
                  A[c3][c4] = ((double )c3) * c4 / ni;
                }
              }
              if (c1 == c2) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c4 = nk; c4 <= nm + -1; c4++) {
                  C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                }
              }
            }
            for (c3 = (nj > nk?nj : nk); c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nm + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) < nl + -1?((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) : nl + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
              if (c1 == c2) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c4 = nk; c4 <= ((16 * c1 + 15 < nl + -1?16 * c1 + 15 : nl + -1)); c4++) {
                  D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
                }
              }
            }
            for (c3 = (((nj > nk?nj : nk)) > nm?((nj > nk?nj : nk)) : nm); c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
            for (c3 = ni; c3 <= ((((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nk + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nk + -1)) < nm + -1?((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nk + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nk + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)) < nm + -1?((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)) : nm + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nm + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nm + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nl > nm?nl : nm); c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= ((((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) < nm + -1?((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nj > nl?nj : nl); c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nj > nm?nj : nm); c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = (ni > nm?ni : nm); c3 <= ((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nk + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
              if (c1 == c2) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c4 = nm; c4 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c4++) {
                  B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                }
              }
            }
            for (c3 = (ni > nj?ni : nj); c3 <= ((((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)) < nm + -1?((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
              if (c1 == c2) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c4 = nj; c4 <= ((16 * c1 + 15 < nl + -1?16 * c1 + 15 : nl + -1)); c4++) {
                  D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
                }
              }
            }
            for (c3 = (((ni > nj?ni : nj)) > nm?((ni > nj?ni : nj)) : nm); c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
            for (c3 = (ni > nk?ni : nk); c3 <= ((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nm + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) < nm + -1?((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
              if (c1 == c2) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c4 = nm; c4 <= ((16 * c1 + 15 < nl + -1?16 * c1 + 15 : nl + -1)); c4++) {
                  D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
                }
              }
            }
            for (c3 = (((ni > nk?ni : nk)) > nm?((ni > nk?ni : nk)) : nm); c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
            for (c3 = (((ni > nj?ni : nj)) > nk?((ni > nj?ni : nj)) : nk); c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)))) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)))) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) && c1 >= ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))) {
          for (c2 = 0; c2 <= (((((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nj + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nj + -1)) < nk + -1?((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nj + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nj + -1)) : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= 16 * c2 + 15; c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
            for (c3 = nj; c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nk + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= 16 * c2 + 15; c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
            for (c3 = nk; c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nj + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= 16 * c2 + 15; c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
            for (c3 = (nj > nk?nj : nk); c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= 16 * c2 + 15; c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
            for (c3 = ni; c3 <= ((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nk + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= 16 * c2 + 15; c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
            for (c3 = (ni > nj?ni : nj); c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= 16 * c2 + 15; c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
            for (c3 = (ni > nk?ni : nk); c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
          }
        }
        if (c1 <= (((((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)))) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)))) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))))) {
          for (c2 = (0 > ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))?0 : ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))); c2 <= (((((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nj + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nj + -1)) < nk + -1?((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nj + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nj + -1)) : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nk + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nk + -1)) < nm + -1?((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nk + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nk + -1)) : nm + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nk + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= ((((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) < nm + -1?((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) : nm + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nj > nm?nj : nm); c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nk; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nm + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nm + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nk > nm?nk : nm); c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nj > nk?nj : nk); c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
            for (c3 = nj; c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nk + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
              if (c1 == c2) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c4 = nj; c4 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c4++) {
                  A[c3][c4] = ((double )c3) * c4 / ni;
                }
              }
            }
            for (c3 = nk; c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nj + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) < nm + -1?((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) : nm + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
              if (c1 == c2) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c4 = nk; c4 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c4++) {
                  C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                }
              }
            }
            for (c3 = (nj > nk?nj : nk); c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
            for (c3 = ni; c3 <= ((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nk + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nm + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nm + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
            for (c3 = (ni > nj?ni : nj); c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
            for (c3 = (ni > nk?ni : nk); c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
          }
        }
        if (c1 <= (((((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))) && c1 >= ((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))))) {
          for (c2 = 0; c2 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nk + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nk + -1)) < nm + -1?((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nk + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nk + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nj > nl?nj : nl); c4 <= 16 * c2 + 15; c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
            for (c3 = nm; c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nk + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= 16 * c2 + 15; c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
            for (c3 = nk; c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nm + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= 16 * c2 + 15; c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
            for (c3 = (nk > nm?nk : nm); c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= 16 * c2 + 15; c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
            for (c3 = ni; c3 <= ((((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)) < nm + -1?((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = (ni > nm?ni : nm); c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
            for (c3 = (ni > nk?ni : nk); c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) && c1 >= ((((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) > ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))?((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) : ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))))) {
          for (c2 = 0; c2 <= (((((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nk + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= 16 * c2 + 15; c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
            for (c3 = nk; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= 16 * c2 + 15; c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
            for (c3 = ni; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
          }
        }
        if (c1 <= (((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) && c1 >= ((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))))) {
          for (c2 = (0 > ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))?0 : ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))); c2 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nk + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= 16 * c2 + 15; c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
            for (c3 = nk; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= 16 * c2 + 15; c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
            for (c3 = ni; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
          }
        }
        if (c1 <= (((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))))) {
          for (c2 = (nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))); c2 <= (((((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nm + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nk + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nk + -1)) < nl + -1?((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nk + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nk + -1)) : nl + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nk + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= ((((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) < nl + -1?((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) : nl + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nj > nl?nj : nl); c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nk; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nk > nl?nk : nl); c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nj > nk?nj : nk); c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = nm; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nk + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nk; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
            for (c3 = ni; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = (ni > nm?ni : nm); c3 <= 16 * c1 + 15; c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
          }
        }
        if (c1 <= (((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) && c1 >= ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))) {
          for (c2 = (nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))); c2 <= (((((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nk + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nk + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nk; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
            for (c3 = nk; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
            for (c3 = ni; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
          }
        }
        if (c1 <= (((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))))) {
          for (c2 = (((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16)))) > ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))?((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16)))) : ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))); c2 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nk + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nk + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nk; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
            for (c3 = nk; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
            for (c3 = ni; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
          }
        }
        if (c1 <= (((((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))) && c1 >= ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))) {
          for (c2 = 0; c2 <= (((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nj + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nj + -1)) < nm + -1?((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nj + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nj + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) < nl + -1?((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) : nl + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nk; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nk > nl?nk : nl); c4 <= 16 * c2 + 15; c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
            for (c3 = nm; c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nj + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nk; c4 <= 16 * c2 + 15; c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
            for (c3 = nj; c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nm + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) < nl + -1?((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) : nl + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nk; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = (nj > nm?nj : nm); c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
            for (c3 = ni; c3 <= ((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nm + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= 16 * c2 + 15; c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
            for (c3 = (ni > nm?ni : nm); c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= 16 * c2 + 15; c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
            for (c3 = (ni > nj?ni : nj); c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)))) && c1 >= ((((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16)))) > ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))?((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16)))) : ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))))) {
          for (c2 = 0; c2 <= (((((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nj + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) < nm + -1?((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) : nm + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nk; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
            for (c3 = nj; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
            for (c3 = ni; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
          }
        }
        if (c1 <= (((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)))) && c1 >= ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))) {
          for (c2 = (0 > ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))?0 : ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))); c2 <= (((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nj + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) < nm + -1?((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) : nm + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nk; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
            for (c3 = nj; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
            for (c3 = ni; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
          }
        }
        if (c1 <= (((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))) && c1 >= ((((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) > ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))?((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) : ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))))) {
          for (c2 = 0; c2 <= (((((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nm + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) < nl + -1?((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) : nl + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nk; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = nm; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
            for (c3 = ni; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) && c1 >= ((((((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) > ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))?((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) : ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16)))))) > ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))?((((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) > ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))?((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) : ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16)))))) : ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))))) {
          for (c2 = 0; c2 <= (((((((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
          }
        }
        if (c1 <= (((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) && c1 >= ((((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) > ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))?((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) : ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))))) {
          for (c2 = (0 > ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))?0 : ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))); c2 <= (((((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
          }
        }
        if (c1 <= (((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) && c1 >= ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))) {
          for (c2 = (nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))); c2 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
          }
        }
        if (c1 <= (((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16))))) {
          for (c2 = (nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))); c2 <= (((((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nj + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) < nl + -1?((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) : nl + -1)) < nm + -1?((((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) < nl + -1?((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) : nl + -1)) : nm + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) < nm + -1?((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) : nm + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) < nl + -1?((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) : nl + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nl > nm?nl : nm); c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nk; c4 <= ((((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) < nm + -1?((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nk > nl?nk : nl); c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nk > nm?nk : nm); c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = nj; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) < nl + -1?((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) : nl + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nk; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = ni; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) < nm + -1?((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = (ni > nj?ni : nj); c3 <= 16 * c1 + 15; c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16))))) {
          for (c2 = (((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) > ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))?((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) : ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))); c2 <= (((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nj + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) < nm + -1?((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) : nm + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nk; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
            for (c3 = nj; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
            for (c3 = ni; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
          }
        }
        if (c1 <= (((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))) && c1 >= ((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))))) {
          for (c2 = (nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))); c2 <= (((((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nm + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) < nl + -1?((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) : nl + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nk; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = nm; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
            for (c3 = ni; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) && c1 >= ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))) {
          for (c2 = (nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))); c2 <= (((((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
          }
        }
        if (c1 <= (((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) && c1 >= ((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))))) {
          for (c2 = (((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) > ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))?((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) : ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))); c2 <= (((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
          }
        }
        if (c1 <= (((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))))) {
          for (c2 = (((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) > ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))?((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) : ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))); c2 <= (((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nm + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) < nl + -1?((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) : nl + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nk; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = nm; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
            for (c3 = ni; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) && c1 >= ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))) {
          for (c2 = (((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) > ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))?((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) : ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))); c2 <= (((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
          }
        }
        if (c1 <= (((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16))) {
          for (c2 = (((((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) > ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))?((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) : ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16)))))) > ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))?((((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) > ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))?((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) : ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16)))))) : ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))); c2 <= (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
          }
        }
        if (c1 <= (((((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))) && c1 >= ((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16))))) {
          for (c2 = 0; c2 <= (((((((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nk + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nk + -1)) < nm + -1?((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nk + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nk + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)) < nm + -1?((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)) : nm + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nm + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nm + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nl > nm?nl : nm); c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= ((((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) < nm + -1?((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nj > nl?nj : nl); c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nj > nm?nj : nm); c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = nm; c3 <= ((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nk + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
              if (c1 == c2) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c4 = nm; c4 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c4++) {
                  B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                }
              }
            }
            for (c3 = nj; c3 <= ((((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)) < nm + -1?((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
              if (c1 == c2) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c4 = nj; c4 <= ((16 * c1 + 15 < nl + -1?16 * c1 + 15 : nl + -1)); c4++) {
                  D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
                }
              }
            }
            for (c3 = (nj > nm?nj : nm); c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
            for (c3 = nk; c3 <= ((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nm + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) < nm + -1?((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
              if (c1 == c2) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c4 = nm; c4 <= ((16 * c1 + 15 < nl + -1?16 * c1 + 15 : nl + -1)); c4++) {
                  D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
                }
              }
            }
            for (c3 = (nk > nm?nk : nm); c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
            for (c3 = (nj > nk?nj : nk); c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) && c1 >= ((((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) > ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))?((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) : ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))))) {
          for (c2 = 0; c2 <= (((((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nk + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= 16 * c2 + 15; c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
            for (c3 = nj; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= 16 * c2 + 15; c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
            for (c3 = nk; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
          }
        }
        if (c1 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) && c1 >= ((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16))))) {
          for (c2 = (0 > ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))?0 : ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))); c2 <= (((((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nk + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nm + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nm + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
            for (c3 = nj; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
            for (c3 = nk; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
          }
        }
        if (c1 <= (((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))) && c1 >= ((((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) > ((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))))?((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) : ((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))))))) {
          for (c2 = 0; c2 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)) < nm + -1?((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = nm; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
            for (c3 = nk; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) && c1 >= ((((((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) > ((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))))?((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) : ((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))))) > ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))?((((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) > ((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))))?((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) : ((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))))) : ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))))) {
          for (c2 = 0; c2 <= (((((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
          }
        }
        if (c1 <= (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) && c1 >= ((((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) > ((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))))?((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) : ((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))))))) {
          for (c2 = (0 > ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))?0 : ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))); c2 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
          }
        }
        if (c1 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)) && c1 >= ((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16))))) {
          for (c2 = (nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))); c2 <= (((((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = nm; c3 <= 16 * c1 + 15; c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
          }
        }
        if (c1 <= (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) && c1 >= ((((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) > ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))?((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) : ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))))) {
          for (c2 = (nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))); c2 <= (((((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
          }
        }
        if (c1 <= (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) && c1 >= ((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16))))) {
          for (c2 = (((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16)))) > ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))?((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16)))) : ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))); c2 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
          }
        }
        if (c1 <= (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))) {
          for (c2 = (nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))); c2 <= (((((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)) < nm + -1?((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)) : nm + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nm + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nm + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nl > nm?nl : nm); c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= ((((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) < nm + -1?((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nj > nl?nj : nl); c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nj > nm?nj : nm); c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = nk; c3 <= 16 * c1 + 15; c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) < nm + -1?((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))) {
          for (c2 = (((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16)))) > ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))?((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16)))) : ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))); c2 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nm + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nm + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
            for (c3 = nk; c3 <= 16 * c1 + 15; c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
          }
        }
        if (c1 <= (((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))))) {
          for (c2 = (((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16)))) > ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))?((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16)))) : ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))); c2 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)) < nm + -1?((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = nm; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
            for (c3 = nk; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) && c1 >= ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))) {
          for (c2 = (nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))); c2 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
          }
        }
        if (c1 <= (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))) {
          for (c2 = (((((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16)))) > ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))?((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16)))) : ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16)))))) > ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))?((((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16)))) > ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))?((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16)))) : ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16)))))) : ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))); c2 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
          }
        }
        if (c1 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))) && c1 >= ((((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) > ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))?((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) : ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))))) {
          for (c2 = 0; c2 <= (((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nm + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= 16 * c2 + 15; c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
            for (c3 = nm; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= 16 * c2 + 15; c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
            for (c3 = nj; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) && c1 >= ((((((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) > ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))?((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) : ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16)))))) > ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))?((((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) > ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))?((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) : ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16)))))) : ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))))) {
          for (c2 = 0; c2 <= (((((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
          }
        }
        if (c1 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) && c1 >= ((((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) > ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))?((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) : ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))))) {
          for (c2 = (0 > ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))?0 : ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))); c2 <= (((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
          }
        }
        if (c1 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) && c1 >= ((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16))))) {
          for (c2 = (nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))); c2 <= (((((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) < nm + -1?((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = nj; c3 <= 16 * c1 + 15; c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) && c1 >= ((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16))))) {
          for (c2 = (((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) > ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))?((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) : ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))); c2 <= (((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
          }
        }
        if (c1 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))) && c1 >= ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))) {
          for (c2 = (nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))); c2 <= (((((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nm + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) < nm + -1?((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = nm; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
            for (c3 = nj; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) && c1 >= ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))) {
          for (c2 = (nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))); c2 <= (((((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
          }
        }
        if (c1 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) && c1 >= ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))) {
          for (c2 = (((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16)))) > ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))?((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16)))) : ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))); c2 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
          }
        }
        if (c1 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16))) {
          for (c2 = (((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) > ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))?((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) : ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))); c2 <= (((((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) < nm + -1?((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = nj; c3 <= 16 * c1 + 15; c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16))) {
          for (c2 = (((((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) > ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))?((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) : ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16)))))) > ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))?((((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) > ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))?((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) : ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16)))))) : ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))); c2 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
          }
        }
        if (c1 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)) && c1 >= ((((((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) > ((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))))?((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) : ((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))))) > ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))?((((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) > ((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))))?((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) : ((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))))) : ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))))) {
          for (c2 = 0; c2 <= (((((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)) && c1 >= ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))) {
          for (c2 = (nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))); c2 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)) && c1 >= ((((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) > ((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))))?((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16)))) : ((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))))))) {
          for (c2 = (nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))); c2 <= (((((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)) && c1 >= ((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16))))) {
          for (c2 = (((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) > ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))?((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) : ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))); c2 <= (((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)) && c1 >= ((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))))) {
          for (c2 = (nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))); c2 <= (((((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))) {
          for (c2 = (((((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) > ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))?((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) : ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16)))))) > ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))?((((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) > ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))?((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) : ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16)))))) : ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))); c2 <= (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
      }
    }
    if (ni >= ((0 > -1 * nj + 1?0 : -1 * nj + 1)) && nj >= 0 && nk >= 1 && nm <= -1) {
#pragma omp parallel for private(c2, c4, c3)
      for (c1 = 0; c1 <= (((((nk + ni + -1) * 16 < 0?((16 < 0?-((-(nk + ni + -1) + 16 + 1) / 16) : -((-(nk + ni + -1) + 16 - 1) / 16))) : (nk + ni + -1) / 16)) < (((nk + ni + nj + -2) * 16 < 0?((16 < 0?-((-(nk + ni + nj + -2) + 16 + 1) / 16) : -((-(nk + ni + nj + -2) + 16 - 1) / 16))) : (nk + ni + nj + -2) / 16))?(((nk + ni + -1) * 16 < 0?((16 < 0?-((-(nk + ni + -1) + 16 + 1) / 16) : -((-(nk + ni + -1) + 16 - 1) / 16))) : (nk + ni + -1) / 16)) : (((nk + ni + nj + -2) * 16 < 0?((16 < 0?-((-(nk + ni + nj + -2) + 16 + 1) / 16) : -((-(nk + ni + nj + -2) + 16 - 1) / 16))) : (nk + ni + nj + -2) / 16)))); c1++) {
        if (c1 <= (((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))))) {
          for (c2 = 0; c2 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nk + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nk + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nk; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
            for (c3 = nk; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
            for (c3 = ni; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
          }
        }
        if (c1 <= (((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) && c1 >= ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))) {
          for (c2 = 0; c2 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
          }
        }
        if (c1 <= (((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16))) {
          for (c2 = (nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))); c2 <= (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
          }
        }
        if (c1 <= (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) && c1 >= ((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16))))) {
          for (c2 = 0; c2 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
          }
        }
        if (c1 <= (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))) {
          for (c2 = (nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))); c2 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
          }
        }
      }
    }
    if (ni >= 0 && nj <= -1 && nk >= ((0 > -1 * nm + 1?0 : -1 * nm + 1)) && nm >= 0) {
#pragma omp parallel for private(c2, c4, c3)
      for (c1 = 0; c1 <= (((ni + nm + -1) * 16 < 0?((16 < 0?-((-(ni + nm + -1) + 16 + 1) / 16) : -((-(ni + nm + -1) + 16 - 1) / 16))) : (ni + nm + -1) / 16)); c1++) {
        if (c1 <= (((((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))))) {
          for (c2 = 0; c2 <= (((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) < nm + -1?((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) < nl + -1?((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)) : nl + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nk; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = nm; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
            for (c3 = ni; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)) && c1 >= ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))) {
          for (c2 = 0; c2 <= (((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
          }
        }
        if (c1 <= (((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16))) {
          for (c2 = (0 > ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))?0 : ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))); c2 <= (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
                A[c3][c4] = ((double )c3) * c4 / ni;
              }
            }
          }
        }
        if (c1 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)) && c1 >= ((ni * 16 < 0?-(-ni / 16) : ((16 < 0?(-ni + - 16 - 1) / - 16 : (ni + 16 - 1) / 16))))) {
          for (c2 = 0; c2 <= (((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))) {
          for (c2 = (nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))); c2 <= (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
      }
    }
    if (nj <= -1 && nk >= 1 && nm <= -1) {
#pragma omp parallel for private(c2, c4, c3)
      for (c1 = 0; c1 <= (((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)); c1++) {
        for (c2 = 0; c2 <= (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)); c2++) {
          for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
            for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nk + -1?16 * c2 + 15 : nk + -1)); c4++) {
              A[c3][c4] = ((double )c3) * c4 / ni;
            }
          }
        }
      }
    }
    if (ni >= 0 && nj >= 0 && nk <= -1 && nm >= 1) {
#pragma omp parallel for private(c2, c4, c3)
      for (c1 = 0; c1 <= (((nj + nm + -1) * 16 < 0?((16 < 0?-((-(nj + nm + -1) + 16 + 1) / 16) : -((-(nj + nm + -1) + 16 - 1) / 16))) : (nj + nm + -1) / 16)); c1++) {
        if (c1 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))))) {
          for (c2 = 0; c2 <= (((((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nm + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) < nm + -1?((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = nm; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
            for (c3 = nj; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) && c1 >= ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))) {
          for (c2 = 0; c2 <= (((((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
          }
        }
        if (c1 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16))) {
          for (c2 = (0 > ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))?0 : ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))); c2 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
          }
        }
        if (c1 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)) && c1 >= ((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))))) {
          for (c2 = 0; c2 <= (((((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))) {
          for (c2 = (nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))); c2 <= (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
      }
    }
    if (ni >= 0 && nj <= -1 && nk <= -1 && nl >= 1) {
#pragma omp parallel for private(c2, c4, c3)
      for (c1 = 0; c1 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)); c1++) {
        for (c2 = 0; c2 <= (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)); c2++) {
          for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
            for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
              D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
            }
          }
        }
      }
    }
    if (ni <= -1 && nj >= ((0 > -1 * nm + 1?0 : -1 * nm + 1)) && nk >= ((0 > -1 * nm + 1?0 : -1 * nm + 1)) && nm >= 0) {
#pragma omp parallel for private(c2, c4, c3)
      for (c1 = 0; c1 <= (((((nk + nj + nm + -1) * 16 < 0?((16 < 0?-((-(nk + nj + nm + -1) + 16 + 1) / 16) : -((-(nk + nj + nm + -1) + 16 - 1) / 16))) : (nk + nj + nm + -1) / 16)) < (((nk + nj + 2 * nm + -2) * 16 < 0?((16 < 0?-((-(nk + nj + 2 * nm + -2) + 16 + 1) / 16) : -((-(nk + nj + 2 * nm + -2) + 16 - 1) / 16))) : (nk + nj + 2 * nm + -2) / 16))?(((nk + nj + nm + -1) * 16 < 0?((16 < 0?-((-(nk + nj + nm + -1) + 16 + 1) / 16) : -((-(nk + nj + nm + -1) + 16 - 1) / 16))) : (nk + nj + nm + -1) / 16)) : (((nk + nj + 2 * nm + -2) * 16 < 0?((16 < 0?-((-(nk + nj + 2 * nm + -2) + 16 + 1) / 16) : -((-(nk + nj + 2 * nm + -2) + 16 - 1) / 16))) : (nk + nj + 2 * nm + -2) / 16)))); c1++) {
        if (c1 <= (((((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))))) {
          for (c2 = 0; c2 <= (((((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nk + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nk + -1)) < nm + -1?((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nk + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nk + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)) < nm + -1?((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)) : nm + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nm + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nm + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nl > nm?nl : nm); c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= ((((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) < nm + -1?((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nj > nl?nj : nl); c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = (nj > nm?nj : nm); c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = nm; c3 <= ((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nk + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
              if (c1 == c2) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c4 = nm; c4 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c4++) {
                  B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                }
              }
            }
            for (c3 = nj; c3 <= ((((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)) < nm + -1?((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
              if (c1 == c2) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c4 = nj; c4 <= ((16 * c1 + 15 < nl + -1?16 * c1 + 15 : nl + -1)); c4++) {
                  D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
                }
              }
            }
            for (c3 = (nj > nm?nj : nm); c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
            for (c3 = nk; c3 <= ((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nm + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) < nm + -1?((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = (nk > nm?nk : nm); c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
            for (c3 = (nj > nk?nj : nk); c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)))) && c1 >= ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))) {
          for (c2 = 0; c2 <= (((((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nk + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= 16 * c2 + 15; c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
            for (c3 = nj; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= 16 * c2 + 15; c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
            for (c3 = nk; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
          }
        }
        if (c1 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))))) {
          for (c2 = (0 > ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))?0 : ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))); c2 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nk + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nm + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nm + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
            for (c3 = nj; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
            for (c3 = nk; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
          }
        }
        if (c1 <= (((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))) && c1 >= ((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))))) {
          for (c2 = 0; c2 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)) < nm + -1?((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = nm; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
            for (c3 = nk; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) && c1 >= ((((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) > ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))?((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) : ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))))) {
          for (c2 = 0; c2 <= (((((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
          }
        }
        if (c1 <= (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) && c1 >= ((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))))) {
          for (c2 = (0 > ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))?0 : ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))); c2 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
          }
        }
        if (c1 <= (((((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))))) {
          for (c2 = (nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))); c2 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)) < nm + -1?((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) < nl + -1?((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)) : nl + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nj; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = nm; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
            for (c3 = nk; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)) && c1 >= ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))) {
          for (c2 = (nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))); c2 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
          }
        }
        if (c1 <= (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16))) {
          for (c2 = (((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16)))) > ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))?((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16)))) : ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))); c2 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
                B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
              }
            }
          }
        }
        if (c1 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))) && c1 >= ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))) {
          for (c2 = 0; c2 <= (((((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nm + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) < nm + -1?((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = nm; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
            for (c3 = nj; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) && c1 >= ((((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16)))) > ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))?((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16)))) : ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))))) {
          for (c2 = 0; c2 <= (((((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
          }
        }
        if (c1 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) && c1 >= ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))) {
          for (c2 = (0 > ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))?0 : ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))); c2 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
          }
        }
        if (c1 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16))) {
          for (c2 = (nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))); c2 <= (((((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) < nm + -1?((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = nj; c3 <= 16 * c1 + 15; c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16))) {
          for (c2 = (((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) > ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))?((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) : ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))); c2 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
          }
        }
        if (c1 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)) && c1 >= ((((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) > ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))?((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) : ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))))) {
          for (c2 = 0; c2 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)) && c1 >= ((nk * 16 < 0?-(-nk / 16) : ((16 < 0?(-nk + - 16 - 1) / - 16 : (nk + 16 - 1) / 16))))) {
          for (c2 = (nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))); c2 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)) && c1 >= ((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))))) {
          for (c2 = (nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))); c2 <= (((((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))) {
          for (c2 = (((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) > ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))?((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16)))) : ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))); c2 <= (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
      }
    }
    if (ni <= -1 && nj >= 1 && nm <= -1) {
#pragma omp parallel for private(c2, c4, c3)
      for (c1 = 0; c1 <= (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)); c1++) {
        for (c2 = 0; c2 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)); c2++) {
          for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nk + -1?16 * c1 + 15 : nk + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
            for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c4++) {
              B[c3][c4] = ((double )c3) * (c4 + 1) / nj;
            }
          }
        }
      }
    }
    if (ni <= -1 && nj <= -1 && nk >= 0 && nl >= 1) {
#pragma omp parallel for private(c2, c4, c3)
      for (c1 = 0; c1 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)); c1++) {
        for (c2 = 0; c2 <= (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)); c2++) {
          for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
            for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
              D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
            }
          }
        }
      }
    }
    if (ni <= -1 && nj >= 0 && nk <= -1 && nm >= 1) {
#pragma omp parallel for private(c2, c4, c3)
      for (c1 = 0; c1 <= (((nj + nm + -1) * 16 < 0?((16 < 0?-((-(nj + nm + -1) + 16 + 1) / 16) : -((-(nj + nm + -1) + 16 - 1) / 16))) : (nj + nm + -1) / 16)); c1++) {
        if (c1 <= (((((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))))) {
          for (c2 = 0; c2 <= (((((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) < nm + -1?((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)) : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) < nm + -1?((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)) : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nl; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = nm; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
            for (c3 = nm; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
            for (c3 = nj; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)) && c1 >= ((nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))))) {
          for (c2 = 0; c2 <= (((((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
          }
        }
        if (c1 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16))) {
          for (c2 = (0 > ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))?0 : ((nl * 16 < 0?-(-nl / 16) : ((16 < 0?(-nl + - 16 - 1) / - 16 : (nl + 16 - 1) / 16))))); c2 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nm + -1?16 * c2 + 15 : nm + -1)); c4++) {
                C[c3][c4] = ((double )c3) * (c4 + 3) / nl;
              }
            }
          }
        }
        if (c1 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)) && c1 >= ((nj * 16 < 0?-(-nj / 16) : ((16 < 0?(-nj + - 16 - 1) / - 16 : (nj + 16 - 1) / 16))))) {
          for (c2 = 0; c2 <= (((((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) < (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))?(((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)) : (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)))); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
        if (c1 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16))) {
          for (c2 = (nm * 16 < 0?-(-nm / 16) : ((16 < 0?(-nm + - 16 - 1) / - 16 : (nm + 16 - 1) / 16))); c2 <= (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)); c2++) {
            for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
                D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
              }
            }
          }
        }
      }
    }
    if (ni <= -1 && nj <= -1 && nk <= -1 && nl >= 1) {
#pragma omp parallel for private(c2, c4, c3)
      for (c1 = 0; c1 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)); c1++) {
        for (c2 = 0; c2 <= (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)); c2++) {
          for (c3 = 16 * c1; c3 <= ((16 * c1 + 15 < nm + -1?16 * c1 + 15 : nm + -1)); c3++) {
#pragma ivdep
#pragma vector always
#pragma simd
            for (c4 = 16 * c2; c4 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c4++) {
              D[c3][c4] = ((double )c3) * (c4 + 2) / nk;
            }
          }
        }
      }
    }
  }
}
/* DCE code. Must scan the entire live-out data.
   Can be used also to check the correctness of the output. */

static void print_array(int ni,int nl,double G[128 + 0][128 + 0])
{
  int i;
  int j;
  for (i = 0; i < ni; i++) 
    for (j = 0; j < nl; j++) {
      fprintf(stderr,"%0.2lf ",G[i][j]);
      if ((i * ni + j) % 20 == 0) 
        fprintf(stderr,"\n");
    }
  fprintf(stderr,"\n");
}
/* Main computational kernel. The whole function will be timed,
   including the call and return. */

static void kernel_3mm(int ni,int nj,int nk,int nl,int nm,double E[128 + 0][128 + 0],double A[128 + 0][128 + 0],double B[128 + 0][128 + 0],double F[128 + 0][128 + 0],double C[128 + 0][128 + 0],double D[128 + 0][128 + 0],double G[128 + 0][128 + 0])
{
  int i;
  int j;
  int k;
  
#pragma scop
{
    int c5;
    int c10;
    int c2;
    int c1;
    int c6;
    int c7;
    if (ni >= 0 && nj >= 0 && nl >= 1) {
#pragma omp parallel for private(c7, c2, c10)
      for (c1 = 0; c1 <= (((nj + ni + -1) * 16 < 0?((16 < 0?-((-(nj + ni + -1) + 16 + 1) / 16) : -((-(nj + ni + -1) + 16 - 1) / 16))) : (nj + ni + -1) / 16)); c1++) {
        for (c2 = 0; c2 <= (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)); c2++) {
          if (c1 <= (((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16))) {
            for (c7 = 16 * c2; c7 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c7++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c10 = 16 * c1; c10 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c10++) {
                G[c10][c7] = 0;
              }
            }
          }
          if (c1 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16))) {
            for (c7 = 16 * c2; c7 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c7++) {
#pragma ivdep
#pragma vector always
#pragma simd
              for (c10 = 16 * c1; c10 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c10++) {
                F[c10][c7] = 0;
              }
            }
          }
        }
      }
    }
    if (ni <= -1 && nl >= 1) {
#pragma omp parallel for private(c7, c2, c10)
      for (c1 = 0; c1 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)); c1++) {
        for (c2 = 0; c2 <= (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)); c2++) {
          for (c7 = 16 * c2; c7 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c7++) {
#pragma ivdep
#pragma vector always
#pragma simd
            for (c10 = 16 * c1; c10 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c10++) {
              F[c10][c7] = 0;
            }
          }
        }
      }
    }
    if (nj <= -1 && nl >= 1) {
#pragma omp parallel for private(c7, c2, c10)
      for (c1 = 0; c1 <= (((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)); c1++) {
        for (c2 = 0; c2 <= (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)); c2++) {
          for (c7 = 16 * c2; c7 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c7++) {
#pragma ivdep
#pragma vector always
#pragma simd
            for (c10 = 16 * c1; c10 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c10++) {
              G[c10][c7] = 0;
            }
          }
        }
      }
    }
    if (nl >= 1 && nm >= 1) {
#pragma omp parallel for private(c7, c6, c2, c10, c5)
      for (c1 = 0; c1 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)); c1++) {
        for (c2 = 0; c2 <= (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)); c2++) {
          for (c5 = 0; c5 <= (((nm + -1) * 16 < 0?((16 < 0?-((-(nm + -1) + 16 + 1) / 16) : -((-(nm + -1) + 16 - 1) / 16))) : (nm + -1) / 16)); c5++) {
            for (c6 = 16 * c5; c6 <= ((16 * c5 + 15 < nm + -1?16 * c5 + 15 : nm + -1)); c6++) {
              for (c7 = 16 * c2; c7 <= ((16 * c2 + 15 < nl + -1?16 * c2 + 15 : nl + -1)); c7++) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c10 = 16 * c1; c10 <= ((16 * c1 + 15 < nj + -1?16 * c1 + 15 : nj + -1)); c10++) {
                  F[c10][c7] += C[c10][c6] * D[c6][c7];
                }
              }
            }
          }
        }
      }
    }
    if (nj >= 1) {
#pragma omp parallel for private(c7, c2, c10)
      for (c1 = 0; c1 <= (((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)); c1++) {
        for (c2 = 0; c2 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)); c2++) {
          for (c7 = 16 * c2; c7 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c7++) {
#pragma ivdep
#pragma vector always
#pragma simd
            for (c10 = 16 * c1; c10 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c10++) {
              E[c10][c7] = 0;
            }
          }
        }
      }
    }
    if (nj >= 1) {
#pragma omp parallel for private(c7, c6, c2, c10, c5)
      for (c1 = 0; c1 <= (((ni + -1) * 16 < 0?((16 < 0?-((-(ni + -1) + 16 + 1) / 16) : -((-(ni + -1) + 16 - 1) / 16))) : (ni + -1) / 16)); c1++) {
        for (c2 = 0; c2 <= (((nj + -1) * 16 < 0?((16 < 0?-((-(nj + -1) + 16 + 1) / 16) : -((-(nj + -1) + 16 - 1) / 16))) : (nj + -1) / 16)); c2++) {
          for (c5 = 0; c5 <= (((nk + -1) * 16 < 0?((16 < 0?-((-(nk + -1) + 16 + 1) / 16) : -((-(nk + -1) + 16 - 1) / 16))) : (nk + -1) / 16)); c5++) {
            for (c6 = 16 * c5; c6 <= ((16 * c5 + 15 < nk + -1?16 * c5 + 15 : nk + -1)); c6++) {
              for (c7 = 16 * c2; c7 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c7++) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c10 = 16 * c1; c10 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c10++) {
                  E[c10][c7] += A[c10][c6] * B[c6][c7];
                }
              }
            }
          }
          for (c5 = 0; c5 <= (((nl + -1) * 16 < 0?((16 < 0?-((-(nl + -1) + 16 + 1) / 16) : -((-(nl + -1) + 16 - 1) / 16))) : (nl + -1) / 16)); c5++) {
            for (c6 = 16 * c5; c6 <= ((16 * c5 + 15 < nl + -1?16 * c5 + 15 : nl + -1)); c6++) {
              for (c7 = 16 * c2; c7 <= ((16 * c2 + 15 < nj + -1?16 * c2 + 15 : nj + -1)); c7++) {
#pragma ivdep
#pragma vector always
#pragma simd
                for (c10 = 16 * c1; c10 <= ((16 * c1 + 15 < ni + -1?16 * c1 + 15 : ni + -1)); c10++) {
                  G[c10][c6] += E[c10][c7] * F[c7][c6];
                }
              }
            }
          }
        }
      }
    }
  }
  
#pragma endscop
}

int main(int argc,char **argv)
{
/* Retrieve problem size. */
  int ni = 128;
  int nj = 128;
  int nk = 128;
  int nl = 128;
  int nm = 128;
/* Variable declaration/allocation. */
  double (*E)[128 + 0][128 + 0];
  E = ((double (*)[128 + 0][128 + 0])(polybench_alloc_data(((128 + 0) * (128 + 0)),(sizeof(double )))));
  ;
  double (*A)[128 + 0][128 + 0];
  A = ((double (*)[128 + 0][128 + 0])(polybench_alloc_data(((128 + 0) * (128 + 0)),(sizeof(double )))));
  ;
  double (*B)[128 + 0][128 + 0];
  B = ((double (*)[128 + 0][128 + 0])(polybench_alloc_data(((128 + 0) * (128 + 0)),(sizeof(double )))));
  ;
  double (*F)[128 + 0][128 + 0];
  F = ((double (*)[128 + 0][128 + 0])(polybench_alloc_data(((128 + 0) * (128 + 0)),(sizeof(double )))));
  ;
  double (*C)[128 + 0][128 + 0];
  C = ((double (*)[128 + 0][128 + 0])(polybench_alloc_data(((128 + 0) * (128 + 0)),(sizeof(double )))));
  ;
  double (*D)[128 + 0][128 + 0];
  D = ((double (*)[128 + 0][128 + 0])(polybench_alloc_data(((128 + 0) * (128 + 0)),(sizeof(double )))));
  ;
  double (*G)[128 + 0][128 + 0];
  G = ((double (*)[128 + 0][128 + 0])(polybench_alloc_data(((128 + 0) * (128 + 0)),(sizeof(double )))));
  ;
/* Initialize array(s). */
  init_array(ni,nj,nk,nl,nm, *A, *B, *C, *D);
/* Start timer. */
  polybench_timer_start();
  ;
/* Run kernel. */
  kernel_3mm(ni,nj,nk,nl,nm, *E, *A, *B, *F, *C, *D, *G);
/* Stop and print timer. */
  polybench_timer_stop();
  ;
  polybench_timer_print();
  ;
/* Prevent dead-code elimination. All live-out data must be printed
     by the function call in argument. */
  if (argc > 42 && !strcmp(argv[0],"")) 
    print_array(ni,nl, *G);
/* Be clean. */
  free(((void *)E));
  ;
  free(((void *)A));
  ;
  free(((void *)B));
  ;
  free(((void *)F));
  ;
  free(((void *)C));
  ;
  free(((void *)D));
  ;
  free(((void *)G));
  ;
  return 0;
}
