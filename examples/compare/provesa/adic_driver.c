#include <string.h>
#include <stdlib.h>
#include <stdio.h>

//#include "ad_grad_reverse.hpp"
#include "ad_types.h"
#include "ad_rev.h"
#include "ad_tape.h"

void ad_o_fcn(DERIV_TYPE *ad_var_ret,DERIV_TYPE *obj,DERIV_TYPE x[6]);

int g_fcn(double *obj, double g_x[6], const double x[6]) {
  int i;
  int j;  
  int ndir = 1;
  DERIV_TYPE  ad_var_ret, ad_obj, ad_x[6];
  int retval;

  // Set indpendent variables 
  ADIC_SetReverseMode();  
  ADIC_Init();
  __ADIC_TapeInit();
  ADIC_SetIndepArray(ad_x,6);
  ADIC_SetDep(ad_obj);
  for(i=0;i<6;i++) {
    DERIV_val(ad_x[i]) = x[i];
  }
  ADIC_SetIndepDone();

  // Invoke AD function 
  our_rev_mode.plain = 0; 
  our_rev_mode.tape = 1; 
  our_rev_mode.adjoint = 0; 
  ad_o_fcn(&ad_var_ret, &ad_obj, ad_x);
  retval = DERIV_val(ad_var_ret);
    
  our_rev_mode.tape = 0; 
  our_rev_mode.adjoint = 1; 
  ad_o_fcn(&ad_var_ret, &ad_obj, ad_x);
  
  *obj = DERIV_val(ad_obj);
  for (i=0;i<6;i++) g_x[i] = DERIV_grad(ad_x[i])[0];
  ADIC_Finalize();  
  return retval;
}
