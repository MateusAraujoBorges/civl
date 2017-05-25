/************************** DISCLAIMER ********************************/
/*                                                                    */
/*   This file was generated on 04/13/17 09:49:48 by                  */
/*   ADIC version /*                                                                    */
/*   ADIC was prepared as an account of work sponsored by an          */
/*   agency of the United States Government and the University of     */
/*   Chicago.  NEITHER THE AUTHOR(S), THE UNITED STATES GOVERNMENT    */
/*   NOR ANY AGENCY THEREOF, NOR THE UNIVERSITY OF CHICAGO, INCLUDING */
/*   ANY OF THEIR EMPLOYEES OR OFFICERS, MAKES ANY WARRANTY, EXPRESS  */
/*   OR IMPLIED, OR ASSUMES ANY LEGAL LIABILITY OR RESPONSIBILITY FOR */
/*   THE ACCURACY, COMPLETENESS, OR USEFULNESS OF ANY INFORMATION OR  */
/*   PROCESS DISCLOSED, OR REPRESENTS THAT ITS USE WOULD NOT INFRINGE */
/*   PRIVATELY OWNED RIGHTS.                                          */
/*                                                                    */
/**********************************************************************/
#ifdef ADIC_DENSE
#include "ad_types.h"
#endif
#ifdef ADIC_DENSE_REVERSE
#include "ad_types.h"
#endif
#ifdef ADIC_DENSE_SEED
#include "ad_types.h"
#endif
#ifdef ADIC_GRAD_LENGTH
#include "ad_grad_length_types.h"
#endif
#ifdef ADIC_SPARSE_NO_GRAD
#include "noderiv_sparslinc.h"
#endif
#ifdef ADIC_SPARSE
#include "sparslinc.h"
#endif
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
#define sqrt3    .577350269189625797959429519858
/*  1.0/sqrt(3.0) */
/*#define tsqrt3  1.15470053837925159591885903972          2.0/sqrt(3.0) */
#define a        .500000000000000000000000000000        /*  1.0/2.0       */
#define b      -1.00000000000000000000000000000        /* -1.0/1.0       */
#define bm1    -2.00000000000000000000000000000        /* -2.0/1.0       */
// = 2.0/sqrt3; 
/* double tsqrt3; */
DERIV_TYPE tsqrt3;
//double tsqrt3 = 2.0/sqrt3; 
/* const */
/*x)*/

void ad_o_fcn(DERIV_TYPE *ad_var_ret,DERIV_TYPE *obj,DERIV_TYPE x[6])
{
  int ad_Symbol_3;
  int ad_Symbol_5;
  int ad_Symbol_4;
  DERIV_TYPE ad_prp_0;
  DERIV_TYPE ad_prp_1;
  DERIV_TYPE ad_prp_4;
  DERIV_TYPE ad_prp_3;
  DERIV_TYPE ad_prp_2;
  DERIV_TYPE ad_prp_5;
  DERIV_TYPE ad_prp_6;
  DERIV_TYPE ad_prp_7;
  DERIV_TYPE ad_prp_10;
  DERIV_TYPE ad_prp_9;
  DERIV_TYPE ad_prp_8;
  DERIV_TYPE ad_prp_11;
  DERIV_TYPE ad_prp_12;
  DERIV_TYPE ad_prp_13;
  DERIV_TYPE ad_prp_14;
  DERIV_TYPE ad_prp_15;
  double ad_Symbol_9;
  double ad_Symbol_8;
  double ad_Symbol_7;
  double ad_Symbol_6;
  DERIV_TYPE ad_prp_18;
  DERIV_TYPE ad_prp_19;
  DERIV_TYPE ad_prp_20;
  DERIV_TYPE ad_prp_21;
  DERIV_TYPE ad_prp_22;
  DERIV_TYPE ad_prp_23;
  DERIV_TYPE ad_prp_24;
  DERIV_TYPE ad_prp_25;
  double ad_Symbol_19;
  double ad_Symbol_18;
  double ad_Symbol_17;
  double ad_Symbol_16;
  double ad_Symbol_15;
  double ad_Symbol_14;
  double ad_Symbol_13;
  double ad_Symbol_12;
  DERIV_TYPE ad_prp_27;
  DERIV_TYPE ad_prp_26;
  double ad_Symbol_11;
  double ad_Symbol_10;
  DERIV_TYPE ad_prp_16;
  int ad_Symbol_0;
  DERIV_TYPE ad_prp_17;
  int ad_Symbol_2;
  double ad_acc_2;
  double ad_lin_13;
  double ad_lin_12;
  double ad_aux_2;
  double ad_lin_11;
  double ad_lin_10;
  double ad_lin_9;
  double ad_lin_8;
  double ad_lin_7;
  double ad_lin_6;
  double ad_lin_5;
  double ad_lin_4;
  int ad_Symbol_1;
  double ad_acc_1;
  double ad_acc_0;
  double ad_lin_3;
  double ad_lin_2;
  double ad_lin_1;
  double ad_lin_0;
  double ad_aux_1;
  double ad_aux_0;
  DERIV_TYPE f;
  DERIV_TYPE g;
  DERIV_TYPE matr[4];
  DERIV_TYPE retval;
  ZeroDeriv(ad_prp_0);
  DERIV_val(ad_prp_0) = 0.00000;
  ZeroDeriv(ad_prp_1);
  DERIV_val(ad_prp_1) = 0.00000;
  ZeroDeriv(ad_prp_4);
  DERIV_val(ad_prp_4) = 0.00000;
  ZeroDeriv(ad_prp_3);
  DERIV_val(ad_prp_3) = 0.00000;
  ZeroDeriv(ad_prp_2);
  DERIV_val(ad_prp_2) = 0.00000;
  ZeroDeriv(ad_prp_5);
  DERIV_val(ad_prp_5) = 0.00000;
  ZeroDeriv(ad_prp_6);
  DERIV_val(ad_prp_6) = 0.00000;
  ZeroDeriv(ad_prp_7);
  DERIV_val(ad_prp_7) = 0.00000;
  ZeroDeriv(ad_prp_10);
  DERIV_val(ad_prp_10) = 0.00000;
  ZeroDeriv(ad_prp_9);
  DERIV_val(ad_prp_9) = 0.00000;
  ZeroDeriv(ad_prp_8);
  DERIV_val(ad_prp_8) = 0.00000;
  ZeroDeriv(ad_prp_11);
  DERIV_val(ad_prp_11) = 0.00000;
  ZeroDeriv(ad_prp_12);
  DERIV_val(ad_prp_12) = 0.00000;
  ZeroDeriv(ad_prp_13);
  DERIV_val(ad_prp_13) = 0.00000;
  ZeroDeriv(ad_prp_14);
  DERIV_val(ad_prp_14) = 0.00000;
  ZeroDeriv(ad_prp_15);
  DERIV_val(ad_prp_15) = 0.00000;
  ZeroDeriv(ad_prp_18);
  DERIV_val(ad_prp_18) = 0.00000;
  ZeroDeriv(ad_prp_19);
  DERIV_val(ad_prp_19) = 0.00000;
  ZeroDeriv(ad_prp_20);
  DERIV_val(ad_prp_20) = 0.00000;
  ZeroDeriv(ad_prp_21);
  DERIV_val(ad_prp_21) = 0.00000;
  ZeroDeriv(ad_prp_22);
  DERIV_val(ad_prp_22) = 0.00000;
  ZeroDeriv(ad_prp_23);
  DERIV_val(ad_prp_23) = 0.00000;
  ZeroDeriv(ad_prp_24);
  DERIV_val(ad_prp_24) = 0.00000;
  ZeroDeriv(ad_prp_25);
  DERIV_val(ad_prp_25) = 0.00000;
  ZeroDeriv(ad_prp_27);
  DERIV_val(ad_prp_27) = 0.00000;
  ZeroDeriv(ad_prp_26);
  DERIV_val(ad_prp_26) = 0.00000;
  ZeroDeriv(ad_prp_16);
  DERIV_val(ad_prp_16) = 0.00000;
  ZeroDeriv(ad_prp_17);
  DERIV_val(ad_prp_17) = 0.00000;
  ZeroDeriv(f);
  DERIV_val(f) = 0.00000;
  ZeroDeriv(g);
  DERIV_val(g) = 0.00000;
  ZeroDerivvector(matr,4);
  SetZeroValvector(matr,4);
  ZeroDeriv(retval);
  DERIV_val(retval) = 0.00000;
  if (our_rev_mode . plain == 1) {
/* static */
/* double matr[4]; double f; double g; double retval; */
    DERIV_TYPE matr[4];
    DERIV_TYPE f;
/* static */
    DERIV_TYPE g;
    DERIV_TYPE retval;
    DERIV_val(retval) = 0.00000;
    DERIV_val(matr[0]) = DERIV_val(x[1]) - DERIV_val(x[0]);
    DERIV_val(matr[1]) = (2.00000 * DERIV_val(x[2]) - DERIV_val(x[1]) - DERIV_val(x[0])) * 0.577350269189625797959429519858;
    DERIV_val(matr[2]) = DERIV_val(x[4]) - DERIV_val(x[3]);
    DERIV_val(matr[3]) = (2.00000 * DERIV_val(x[5]) - DERIV_val(x[4]) - DERIV_val(x[3])) * 0.577350269189625797959429519858;
    DERIV_val(g) = DERIV_val(matr[0]) * DERIV_val(matr[3]) - DERIV_val(matr[1]) * DERIV_val(matr[2]);
    if (DERIV_val(g) <= 1.00000e-14) {
      DERIV_val( *obj) = DERIV_val(g);
      DERIV_val(retval) = 1.00000;
    }
     else {
      DERIV_val(f) = DERIV_val(matr[0]) * DERIV_val(matr[0]) + DERIV_val(matr[1]) * DERIV_val(matr[1]) + DERIV_val(matr[2]) * DERIV_val(matr[2]) + DERIV_val(matr[3]) * DERIV_val(matr[3]);
      DERIV_val( *obj) = 0.500000 * DERIV_val(f) / DERIV_val(g);
    }
    DERIV_val( *ad_var_ret) = DERIV_val(retval);
  }
   else if (our_rev_mode . tape == 1) {
/* static */
/* double matr[4]; double f; double g; double retval; */
    DERIV_TYPE matr[4];
    DERIV_TYPE f;
/* static */
    DERIV_TYPE g;
    DERIV_TYPE retval;
    DERIV_val(retval) = 0.00000;
    DERIV_val(matr[0]) = DERIV_val(x[1]) - DERIV_val(x[0]);
    ad_aux_0 = 2.00000 * DERIV_val(x[2]) - DERIV_val(x[1]) - DERIV_val(x[0]);
    DERIV_val(matr[1]) = ad_aux_0 * 0.577350269189625797959429519858;
    DERIV_val(matr[2]) = DERIV_val(x[4]) - DERIV_val(x[3]);
    ad_aux_1 = 2.00000 * DERIV_val(x[5]) - DERIV_val(x[4]) - DERIV_val(x[3]);
    DERIV_val(matr[3]) = ad_aux_1 * 0.577350269189625797959429519858;
    ad_lin_0 = DERIV_val(matr[3]);
    ad_lin_1 = DERIV_val(matr[0]);
    ad_lin_2 = DERIV_val(matr[2]);
    ad_lin_3 = DERIV_val(matr[1]);
    DERIV_val(g) = DERIV_val(matr[0]) * DERIV_val(matr[3]) - DERIV_val(matr[1]) * DERIV_val(matr[2]);
    ad_acc_0 = ad_lin_2 * -1;
    ad_acc_1 = ad_lin_3 * -1;
    push_s0(ad_lin_0);
    push_s0(ad_lin_1);
    push_s0(ad_acc_0);
    push_s0(ad_acc_1);
    if (DERIV_val(g) <= 1.00000e-14) {
      DERIV_val( *obj) = DERIV_val(g);
      DERIV_val(retval) = 1.00000;
      ad_Symbol_1 = 1;
      push_i_s0(ad_Symbol_1);
    }
     else {
      ad_lin_4 = DERIV_val(matr[0]);
      ad_lin_5 = DERIV_val(matr[0]);
      ad_lin_6 = DERIV_val(matr[1]);
      ad_lin_7 = DERIV_val(matr[1]);
      ad_lin_8 = DERIV_val(matr[2]);
      ad_lin_9 = DERIV_val(matr[2]);
      ad_lin_10 = DERIV_val(matr[3]);
      ad_lin_11 = DERIV_val(matr[3]);
      DERIV_val(f) = DERIV_val(matr[0]) * DERIV_val(matr[0]) + DERIV_val(matr[1]) * DERIV_val(matr[1]) + DERIV_val(matr[2]) * DERIV_val(matr[2]) + DERIV_val(matr[3]) * DERIV_val(matr[3]);
      push_s0(ad_lin_4);
      push_s0(ad_lin_5);
      push_s0(ad_lin_6);
      push_s0(ad_lin_7);
      push_s0(ad_lin_8);
      push_s0(ad_lin_9);
      push_s0(ad_lin_10);
      push_s0(ad_lin_11);
      ad_aux_2 = 0.500000 * DERIV_val(f);
      ad_lin_12 = 1.00000 / DERIV_val(g);
      ad_lin_13 = -(ad_aux_2 / (DERIV_val(g) * DERIV_val(g)));
      DERIV_val( *obj) = ad_aux_2 / DERIV_val(g);
      ad_acc_2 = 0.500000 * ad_lin_12;
      push_s0(ad_lin_13);
      push_s0(ad_acc_2);
      ad_Symbol_2 = 0;
      push_i_s0(ad_Symbol_2);
    }
    DERIV_val( *ad_var_ret) = DERIV_val(retval);
  }
   else if (our_rev_mode . adjoint == 1) {
    IncDeriv(ad_prp_17, *ad_var_ret);
    ZeroDeriv( *ad_var_ret);
    IncDeriv(retval,ad_prp_17);
    ZeroDeriv(ad_prp_17);
    pop_i_s0(ad_Symbol_0);
    if (ad_Symbol_0 != 0) {
      IncDeriv(ad_prp_16, *obj);
      ZeroDeriv( *obj);
      IncDeriv(g,ad_prp_16);
      ZeroDeriv(ad_prp_16);
      ZeroDeriv(retval);
    }
     else {
      pop_s0(ad_Symbol_10);
      pop_s0(ad_Symbol_11);
      Saxpy(ad_Symbol_10, *obj,ad_prp_26);
      Saxpy(ad_Symbol_11, *obj,ad_prp_27);
      ZeroDeriv( *obj);
      IncDeriv(g,ad_prp_27);
      ZeroDeriv(ad_prp_27);
      IncDeriv(f,ad_prp_26);
      ZeroDeriv(ad_prp_26);
      pop_s0(ad_Symbol_12);
      pop_s0(ad_Symbol_13);
      pop_s0(ad_Symbol_14);
      pop_s0(ad_Symbol_15);
      pop_s0(ad_Symbol_16);
      pop_s0(ad_Symbol_17);
      pop_s0(ad_Symbol_18);
      pop_s0(ad_Symbol_19);
      Saxpy(ad_Symbol_12,f,ad_prp_25);
      Saxpy(ad_Symbol_13,f,ad_prp_24);
      Saxpy(ad_Symbol_14,f,ad_prp_23);
      Saxpy(ad_Symbol_15,f,ad_prp_22);
      Saxpy(ad_Symbol_16,f,ad_prp_21);
      Saxpy(ad_Symbol_17,f,ad_prp_20);
      Saxpy(ad_Symbol_18,f,ad_prp_19);
      Saxpy(ad_Symbol_19,f,ad_prp_18);
      ZeroDeriv(f);
      IncDeriv(matr[3],ad_prp_25);
      ZeroDeriv(ad_prp_25);
      IncDeriv(matr[3],ad_prp_24);
      ZeroDeriv(ad_prp_24);
      IncDeriv(matr[2],ad_prp_23);
      ZeroDeriv(ad_prp_23);
      IncDeriv(matr[2],ad_prp_22);
      ZeroDeriv(ad_prp_22);
      IncDeriv(matr[1],ad_prp_21);
      ZeroDeriv(ad_prp_21);
      IncDeriv(matr[1],ad_prp_20);
      ZeroDeriv(ad_prp_20);
      IncDeriv(matr[0],ad_prp_19);
      ZeroDeriv(ad_prp_19);
      IncDeriv(matr[0],ad_prp_18);
      ZeroDeriv(ad_prp_18);
    }
    pop_s0(ad_Symbol_6);
    pop_s0(ad_Symbol_7);
    pop_s0(ad_Symbol_8);
    pop_s0(ad_Symbol_9);
    Saxpy(ad_Symbol_6,g,ad_prp_15);
    Saxpy(ad_Symbol_7,g,ad_prp_14);
    Saxpy(ad_Symbol_8,g,ad_prp_13);
    Saxpy(ad_Symbol_9,g,ad_prp_12);
    ZeroDeriv(g);
    IncDeriv(matr[2],ad_prp_15);
    ZeroDeriv(ad_prp_15);
    IncDeriv(matr[1],ad_prp_14);
    ZeroDeriv(ad_prp_14);
    IncDeriv(matr[3],ad_prp_13);
    ZeroDeriv(ad_prp_13);
    IncDeriv(matr[0],ad_prp_12);
    ZeroDeriv(ad_prp_12);
    Saxpy(0.577350269189625797959429519858,matr[3],ad_prp_11);
    ZeroDeriv(matr[3]);
    Saxpy(2.00000,ad_prp_11,ad_prp_8);
    DecDeriv(ad_prp_9,ad_prp_11);
    DecDeriv(ad_prp_10,ad_prp_11);
    ZeroDeriv(ad_prp_11);
    IncDeriv(x[3],ad_prp_10);
    ZeroDeriv(ad_prp_10);
    IncDeriv(x[4],ad_prp_9);
    ZeroDeriv(ad_prp_9);
    IncDeriv(x[5],ad_prp_8);
    ZeroDeriv(ad_prp_8);
    DecDeriv(ad_prp_7,matr[2]);
    IncDeriv(ad_prp_6,matr[2]);
    ZeroDeriv(matr[2]);
    IncDeriv(x[3],ad_prp_7);
    ZeroDeriv(ad_prp_7);
    IncDeriv(x[4],ad_prp_6);
    ZeroDeriv(ad_prp_6);
    Saxpy(0.577350269189625797959429519858,matr[1],ad_prp_5);
    ZeroDeriv(matr[1]);
    Saxpy(2.00000,ad_prp_5,ad_prp_2);
    DecDeriv(ad_prp_3,ad_prp_5);
    DecDeriv(ad_prp_4,ad_prp_5);
    ZeroDeriv(ad_prp_5);
    IncDeriv(x[0],ad_prp_4);
    ZeroDeriv(ad_prp_4);
    IncDeriv(x[1],ad_prp_3);
    ZeroDeriv(ad_prp_3);
    IncDeriv(x[2],ad_prp_2);
    ZeroDeriv(ad_prp_2);
    DecDeriv(ad_prp_1,matr[0]);
    IncDeriv(ad_prp_0,matr[0]);
    ZeroDeriv(matr[0]);
    IncDeriv(x[0],ad_prp_1);
    ZeroDeriv(ad_prp_1);
    IncDeriv(x[1],ad_prp_0);
    ZeroDeriv(ad_prp_0);
    ZeroDeriv(retval);
  }
}
