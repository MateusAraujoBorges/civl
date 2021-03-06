/*        Generated by TAPENADE     (INRIA, Ecuador team)
    Tapenade 3.12 (r6213) - 13 Oct 2016 10:54
*/
#include "GlobalDeclarations_bv.c"
#include "DIFFSIZES.inc"
/*  Hint: NBDirsMax should be the maximum number of differentiation directions
*/

/*
  Differentiation of o_fcn in reverse (adjoint) mode:
   gradient     of useful results: *obj
   with respect to varying inputs: *obj x[0:6-1]
   RW status of diff variables: *obj:in-out x[0:6-1]:out
   Plus diff mem management of: obj:in x:in
*/
// = 2.0/sqrt3; 
//double tsqrt3 = 2.0/sqrt3; 
void o_fcn_bv(double *obj, double (*objb)[NBDirsMax], double x[6], double xb[6
        ][NBDirsMax], int nbdirs) {
    /* const 
 static */
    double matr[4], f;
    double matrb[4][NBDirsMax], fb[NBDirsMax];
    /* static */
    double g;
    double gb[NBDirsMax];
    double retval;
    int nd;
    int ii1;
    double tempb[NBDirsMax];
    double tempb0[NBDirsMax];
    double tempb1[NBDirsMax];
    double o_fcn;
    /* Calculate M = A*inv(W). */
    matr[0] = x[1] - x[0];
    matr[1] = (2.0*x[2]-x[1]-x[0])*.577350269189625797959429519858;
    matr[2] = x[4] - x[3];
    matr[3] = (2.0*x[5]-x[4]-x[3])*.577350269189625797959429519858;
    /* Calculate det(M). */
    g = matr[0]*matr[3] - matr[1]*matr[2];
    if (g <= 1.00000e-14) {
        for (nd = 0; nd < nbdirs; ++nd) {
            gb[nd] = *objb[nd];
            *objb[nd] = 0.0;
        }
        for (nd = 0; nd < nbdirs; ++nd)
            for (ii1 = 0; ii1 < 4; ++ii1)
                matrb[ii1][nd] = 0.0;
    } else {
        /* Calculate norm(M). */
        f = matr[0]*matr[0] + matr[1]*matr[1] + matr[2]*matr[2] + matr[3]*matr
            [3];
        /* Calculate objective function. */
        for (nd = 0; nd < nbdirs; ++nd) {
            tempb1[nd] = .500000000000000000000000000000*(*objb[nd])/g;
            fb[nd] = tempb1[nd];
            gb[nd] = -(f*tempb1[nd]/g);
            *objb[nd] = 0.0;
            for (ii1 = 0; ii1 < 4; ++ii1)
                matrb[ii1][nd] = 0.0;
            matrb[0][nd] = matrb[0][nd] + 2*matr[0]*fb[nd];
            matrb[1][nd] = matrb[1][nd] + 2*matr[1]*fb[nd];
            matrb[2][nd] = matrb[2][nd] + 2*matr[2]*fb[nd];
            matrb[3][nd] = matrb[3][nd] + 2*matr[3]*fb[nd];
        }
    }
    for (nd = 0; nd < nbdirs; ++nd) {
        matrb[0][nd] = matrb[0][nd] + matr[3]*gb[nd];
        matrb[3][nd] = matrb[3][nd] + matr[0]*gb[nd];
        matrb[1][nd] = matrb[1][nd] - matr[2]*gb[nd];
        matrb[2][nd] = matrb[2][nd] - matr[1]*gb[nd];
        for (ii1 = 0; ii1 < 6; ++ii1)
            xb[ii1][nd] = 0.0;
        tempb[nd] = .577350269189625797959429519858*matrb[3][nd];
        xb[5][nd] = xb[5][nd] + 2.0*tempb[nd];
        xb[4][nd] = xb[4][nd] - tempb[nd];
        xb[3][nd] = xb[3][nd] - tempb[nd];
        matrb[3][nd] = 0.0;
        xb[4][nd] = xb[4][nd] + matrb[2][nd];
        xb[3][nd] = xb[3][nd] - matrb[2][nd];
        matrb[2][nd] = 0.0;
        tempb0[nd] = .577350269189625797959429519858*matrb[1][nd];
        xb[2][nd] = xb[2][nd] + 2.0*tempb0[nd];
        xb[1][nd] = xb[1][nd] - tempb0[nd];
        xb[0][nd] = xb[0][nd] - tempb0[nd];
        matrb[1][nd] = 0.0;
        xb[1][nd] = xb[1][nd] + matrb[0][nd];
        xb[0][nd] = xb[0][nd] - matrb[0][nd];
    }
}
/****************************************************************************
 This set of functions reference triangular elements to an equilateral     
 triangle.  The input are the coordinates in the following order:          
      [x1 x2 x3 y1 y2 y3]                                                  
 A zero return value indicates success, while a nonzero value indicates    
 failure.                                                                  
***************************************************************************
 Not all compilers substitute out constants (especially the square root).  
 Therefore, they are substituted out manually.  The values below were      
 calculated on a solaris machine using long doubles. I believe they are    
 accurate.                                                                 
***************************************************************************
 #define sqrt3    .577350269189625797959429519858         1.0/sqrt(3.0) 
#define tsqrt3  1.15470053837925159591885903972          2.0/sqrt(3.0) */
double tsqrt3;
