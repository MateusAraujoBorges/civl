/*!#########################################################
! This file is part of OpenAD released under the LGPL.   #
! The full COPYRIGHT notice can be found in the top      #
! level directory of the OpenAD distribution             #
!#########################################################
*/

#include <stdio.h>
#include "ad_tape.h"

/* Globals */
double __ADIC_double_tape[max_double_tape_size] =  {0};
int    __ADIC_integer_tape[max_integer_tape_size] = {0};
int    __ADIC_logical_tape[max_logical_tape_size] = {0};
char*  __ADIC_character_tape[max_character_tape_size] = {0};
int    __ADIC_stringlength_tape[max_stringlength_tape_size] = {0};

  int __ADIC_double_tape_pointer= 0, __ADIC_integer_tape_pointer = 0 , __ADIC_logical_tape_pointer = 0, __ADIC_character_tape_pointer = 0, __ADIC_stringlength_tape_pointer =0;


  void __ADIC_TapeInit()
  {
      __ADIC_double_tape_pointer       = 0;
      __ADIC_integer_tape_pointer      = 0;
    __ADIC_logical_tape_pointer      = 0;
    __ADIC_character_tape_pointer    = 0;
    __ADIC_stringlength_tape_pointer = 0;
   }

  

  void __ADIC_TapeDump()
  {
    int i;
    printf("\n double tape");
    for (i=0; i < __ADIC_double_tape_pointer; i++)
      printf("\n %lf", __ADIC_double_tape[i]);

    printf("\n integer tape");
    for(i=0; i < __ADIC_integer_tape_pointer; i++)
      printf("\n %d", __ADIC_integer_tape[i]);

    printf("\n logical tape");
    for(i=0; i < __ADIC_logical_tape_pointer; i++)
      printf("\n %d", __ADIC_logical_tape[i]);
      
  }



