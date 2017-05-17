#define epsilon 1.00000e-14

/*****************************************************************************/
/* This set of functions reference triangular elements to an equilateral     */
/* triangle.  The input are the coordinates in the following order:          */
/*      [x1 x2 x3 y1 y2 y3]                                                  */
/* A zero return value indicates success, while a nonzero value indicates    */
/* failure.                                                                  */
/*****************************************************************************/
/* Not all compilers substitute out constants (especially the square root).  */
/* Therefore, they are substituted out manually.  The values below were      */
/* calculated on a solaris machine using long doubles. I believe they are    */
/* accurate.                                                                 */
/*****************************************************************************/

 #define sqrt3    .577350269189625797959429519858         /*1.0/sqrt(3.0) */ 
/*#define tsqrt3  1.15470053837925159591885903972          2.0/sqrt(3.0) */
#define a        .500000000000000000000000000000        /*  1.0/2.0       */
#define b      -1.00000000000000000000000000000        /* -1.0/1.0       */
#define bm1    -2.00000000000000000000000000000        /* -2.0/1.0       */

 double tsqrt3;// = 2.0/sqrt3; 
 //double tsqrt3 = 2.0/sqrt3; 

double o_fcn(double *obj, /* const */ double x[6])
{
 /* static */ double matr[4], f;
 /* static */ double g;
 double retval;

 retval = 0.0;

 /* Calculate M = A*inv(W). */
 matr[0] = x[1] - x[0];
 matr[1] = (2.0*x[2] - x[1] - x[0])*sqrt3;

 matr[2] = x[4] - x[3];
 matr[3] = (2.0*x[5] - x[4] - x[3])*sqrt3;

 /* Calculate det(M). */
 g = matr[0]*matr[3] - matr[1]*matr[2];
 if (g <= epsilon) { *obj = g; retval = 1.0; }
 else {
 /* Calculate norm(M). */
 f = matr[0]*matr[0] + matr[1]*matr[1] + 
     matr[2]*matr[2] + matr[3]*matr[3];

 /* Calculate objective function. */
 (*obj) = a * f / g;
 }
 return retval;
}

