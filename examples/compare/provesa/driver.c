/***
 * IMPORTANT: Change the values of the variables marked by 'CHANGEME'
 ***/

#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#ifdef _CIVL
$input	double	global_x[6];
$output	int    	global_retval;
$output	double 	global_f;
$output	double	global_grad[6]; 
#else
//#pragma CIVL input
double          global_x[6];
//#pragma CIVL output
int             global_retval;
//#pragma CIVL output
double          global_f;
//#pragma CIVL output
double          global_grad[6];
#endif

int g_fcn(double *obj, double g_x[6], const double x[6]);

int main(void) {
  double x[6],obj,gradient[6];
  int retval;
  int i;

  #ifndef _CIVL
    for (i=0;i<6;i++) global_x[i] = pow(i,0.6); //i*1.00000e-8; //pow(i,0.6);
  #endif
  printf("====================  INPUT STARTS HERE ====================\n");
  for (i=0;i<6;i++) printf("global_x[%d] = %f\n", i, global_x[i]);
  printf("====================  INPUT ENDS HERE ====================\n");
  for (i=0;i<6;i++) x[i] = global_x[i];
  retval = g_fcn(&obj,gradient,x);
  global_retval = retval;
  #ifdef _CIVL
  printf("====================  RESULT STARTS HERE ====================\n");
  #endif
  printf("global_retval=%d\n", retval);
  global_f = obj;
  //printf("global_f=%f\n", obj);
  for (i=0;i<6;i++) global_grad[i] = gradient[i];
  for (i=0;i<6;i++) printf("global_grad[%d]=%f\n", i, gradient[i]);
  #ifdef _CIVL
  printf("==================== RESULT ENDS HERE ====================\n");
  #endif
  return 0;
}
