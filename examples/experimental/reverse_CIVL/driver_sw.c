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
//    for (i=0;i<6;i++) global_x[i] = pow(i,0.6);
  FILE* f1 = fopen("x.in", "r");
  double in = 0;
  i = 0;
  while( fscanf(f1, "%lf,", &in) > 0 ) // parse %d followed by ','
  {
      global_x[i++] = in;
  }
  fclose(f1);

  #endif
//  printf("====================  INPUT STARTS HERE ====================\n");
//  for (i=0;i<6;i++) printf("global_x[%d] = %f\n", i, global_x[i]);
//  printf("====================  INPUT ENDS HERE ====================\n");
  for (i=0;i<6;i++) x[i] = global_x[i];
// Flip second and third vertices if determinant is negative
   if ((x[1]-x[0])*(x[5]-x[3])-(x[4]-x[3])*(x[2]-x[0]) < 0.0) 
   {
	obj  = x[1];
	x[1] = x[2];
	x[2] = obj;
	obj  = x[4];
   	x[4] = x[5];
 	x[5] = obj;
   }

  retval = g_fcn(&obj,gradient,x);
  global_retval = retval;
  #ifdef _CIVL
//  printf("====================  RESULT STARTS HERE ====================\n");
  #endif
//  printf("global_retval=%d\n", retval);
  global_f = obj;
  //printf("global_f=%f\n", obj);
  for (i=0;i<6;i++) global_grad[i] = gradient[i];

  FILE* f2 = fopen("g.out", "w");
  fprintf(f2, "%d\n", retval);
  for (i=0;i<6;i++) fprintf(f2, "%.17g\n", gradient[i]);
  fclose(f2);

//  for (i=0;i<6;i++) printf("global_grad[%d]=%f\n", i, gradient[i]);
  #ifdef _CIVL
//  printf("==================== RESULT ENDS HERE ====================\n");
  #endif
  return 0;
}
