/* Simplified transformation example from Devito compiler.
 */
#include <stdio.h>
#ifdef _CIVL
#include <civlc.cvh>
#endif

#ifdef _CIVL
$input int ni;
$input int nj;
$assume(ni>0);
$assume(ni<10);
$assume(nj>0);
$assume(nj<10);
$input double uin[ni][nj];
#endif
double u1[ni][nj];
double u2[ni][nj];

int main(int argc, char** argv) {
  int i,j,ir,jr;

  for(i=0;i<ni;i++) {
    for(j=0;j<nj;j++) {
      u1[i][j] = 0;
      u2[i][j] = 0;
    }
  }

  // straightforward loop nest
  for(i=1;i<ni-1;i++) {
    for(j=1;j<nj-1;j++) {
      u1[i][j] = uin[i][j]*uin[i][j];
    }
  }

  if (ni > 2) {
    $assert(i == ni - 1);	
    if (nj > 2)
      $assert(j == nj - 1);
    else
      $assert(j == 1);
  } else {
    $assert(i == 1);
    $assert(j == nj);
  }

  // blocked loop nest
  for(i=1;i<ni-2;i=i+2) {
    for(j=1;j<nj-2;j=j+2) {
      u2[i][j] = uin[i][j]*uin[i][j];
      u2[i+1][j] = uin[i+1][j]*uin[i+1][j];
      u2[i][j+1] = uin[i][j+1]*uin[i][j+1];
      u2[i+1][j+1] = uin[i+1][j+1]*uin[i+1][j+1];
    }
  }
  // remainder
  if(i==ni-2) {
    for(jr=1;jr<nj-1;jr++) {
      u2[i][jr] = uin[i][jr]*uin[i][jr];
    }
  }
  if(j==nj-2) {
    for(ir=1;ir<ni-1;ir++) {
      u2[ir][j] = uin[ir][j]*uin[ir][j];
    }
  }
  if(i==ni-2 && j==nj-2) u2[i][j] = uin[i][j]*uin[i][j];


  // print
  printf("j = %d\n", j);
  printf("uout1:%s","\n");
  for(i=0;i<ni;i++) {
    for(j=0;j<nj;j++) {
      printf("%f ",u1[i][j]);
    }
    printf("\n");
  }
  printf("uout2:%s","\n");
  for(i=0;i<ni;i++) {
    for(j=0;j<nj;j++) {
      printf("%f ",u2[i][j]);
    }
    printf("\n");
  }
  
  // assert equality of u1 and u2
  for(i=0;i<ni;i++) {
    for(j=0;j<nj;j++) {
      $assert(u1[i][j] == u2[i][j]);
    }
  }
}
