#ifndef _CIVL
#include <cassert>
#include <cstdlib>
#include <cmath>
#include <iostream>
#include <fstream>
#include <vector>
#include <cstdio>
#include <string>
#include <inttypes.h>
#include <sys/time.h>
#include <math.h>
#include <omp.h>
#endif


#ifdef _CIVL
#include <civlc.cvh>
#include <stdio.h>
#include <assert.h>
#include <omp.h>
#endif


const int sz = 8;
const int st = 10;


#ifdef _CIVL
$input float uvecin[sz*st*sz];
#else
float uvecin[st*sz*sz];
#endif




int OperatorSerial(float *u_vec)
{
#ifdef _CIVL
  float *u[st][sz];
  for(int i3=0; i3<st; i3++) {
    for(int i2=0; i2<sz; i2++) {
      u[i3][i2] = &u_vec[i3*sz*sz+i2*sz];
    }
  }
#else
  float (*u)[sz][sz] = (float (*)[sz][sz]) u_vec;
#endif
  {
    int t0;
    int t1;
    for (int i3 = 0; i3<st; i3+=1)
    {
      {
        t0 = (i3)%(2);
        t1 = (t0 + 1)%(2);
      }
      {
        for (int i1 = 1; i1<sz-1; i1++)
        {
          #pragma GCC ivdep
          for (int i2 = 1; i2<sz-1; i2++)
          {
            u[t1][i1][i2] = 2.5e-1F*u[t0][i1][i2 - 1] + 2.5e-1F*u[t0][i1][i2 + 1] + 2.5e-1F*u[t0][i1 - 1][i2] + 2.5e-1F*u[t0][i1 + 1][i2];
          }
        }
      }
    }
  }
  return 0;
}




int OperatorParall(float *u_vec)
{
#ifdef _CIVL
  float *u[st][sz];
  for(int i3=0; i3<st; i3++) {
    for(int i2=0; i2<sz; i2++) {
      u[i3][i2] = &u_vec[i3*sz*sz+i2*sz];
    }
  }
#else
  float (*u)[sz][sz] = (float (*)[sz][sz]) u_vec;
#endif
  {
    int t0;
    int t1;
    #pragma omp parallel
    for (int i3 = 0; i3<st; i3+=1)
    {
      #pragma omp single
      {
        t0 = (i3)%(2);
        t1 = (t0 + 1)%(2);
      }
      {
        #pragma omp for schedule(static)
        for (int i1 = 1; i1<sz-1; i1++)
        {
          //#pragma omp simd aligned(u:64)
          for (int i2 = 1; i2<sz-1; i2++)
          {
            u[t1][i1][i2] = 2.5e-1F*u[t0][i1][i2 - 1] + 2.5e-1F*u[t0][i1][i2 + 1] + 2.5e-1F*u[t0][i1 - 1][i2] + 2.5e-1F*u[t0][i1 + 1][i2];
          }
        }
      }
    }
  }
  return 0;
}


int main(int argc, char** argv) {
  printf("alive A\n");
  float uvecoutserial[st*sz*sz];
  float uvecoutparall[st*sz*sz];
  printf("alive B\n");
  #ifndef _CIVL
  for (int i = 0; i<st*sz*sz; i++) {
    uvecin[i] = 0.0;
  }
  #endif
  printf("alive C\n");
  for (int i = 0; i<st*sz*sz; i++) {
    uvecoutserial[i] = uvecin[i];
    uvecoutparall[i] = uvecin[i];
  }
  printf("alive D\n");
  OperatorSerial(&uvecoutserial[0]);
  OperatorParall(&uvecoutparall[0]);
  printf("alive E\n");
  for (int i = 0; i<st*sz*sz; i++) {
    printf("%f %f \n",uvecoutserial[i], uvecoutparall[i]);
    assert(uvecoutserial[i] == uvecoutparall[i]);
  }
  printf("alive F\n");
  return 0;
}
