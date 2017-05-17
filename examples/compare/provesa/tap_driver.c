#include <stdio.h>
#include "DIFFSIZES.inc"

void o_fcn_bv(double *obj, double (*objb)[NBDirsMax], double x[6], double xb[6][NBDirsMax], int nbdirs);

int g_fcn(double *obj, double g_obj[6], const double cx[6])
{
    double xb[6][NBDirsMax], objb[NBDirsMax];
    int i, j;
    int o_fcn = 0   ;
    int nbdirs;
    double x[6];
    nbdirs = NBDirsMax;
    for(i=0;i<6;i++) {
        x[i] = cx[i];
    }
    for(i=0;i<NBDirsMax;i++) {
      objb[i] = 1.0;
    }
    for(i=0;i<6;i++) {
      for(j=0;j<NBDirsMax;j++) {
       xb[i][j] = 0.0;
      }
    }
    
    o_fcn_bv(obj, &objb, x, xb, nbdirs);

    //SHK: Forced to add this line
    *obj = 0.0;
    
    for(i=0;i<6;i++) g_obj[i] = xb[i][0];
    return o_fcn;
}
