/*!#########################################################
! This file is part of OpenAD released under the LGPL.   #
! The full COPYRIGHT notice can be found in the top      #
! level directory of the OpenAD distribution             #
!#########################################################
*/
 #ifndef __AD_TAPE_HPP_
 #define __AD_TAPE_HPP_
 
// #define max_double_tape_size  10000000
// #define max_integer_tape_size 10000000
// #define max_logical_tape_size 10000
// #define max_character_tape_size 1000000
// #define max_stringlength_tape_size 1000

#define max_double_tape_size  100
#define max_integer_tape_size 100
#define max_logical_tape_size 100
#define max_character_tape_size 100
#define max_stringlength_tape_size 1000

  void __ADIC_TapeInit();
  void __ADIC_Dump();
  void __ADIC_TapeDump();


  extern double __ADIC_double_tape[max_double_tape_size];
  extern int    __ADIC_integer_tape[max_integer_tape_size];
  extern int    __ADIC_logical_tape[max_logical_tape_size];
  extern char*  __ADIC_character_tape[max_character_tape_size];
  extern int    __ADIC_stringlength_tape[max_stringlength_tape_size];

  extern int __ADIC_double_tape_pointer;
  extern int  __ADIC_integer_tape_pointer;
  extern int  __ADIC_logical_tape_pointer;
  extern int  __ADIC_character_tape_pointer;
  extern int  __ADIC_stringlength_tape_pointer; 

#define push_s0(var)                                               \
{                                                               \
     __ADIC_double_tape[__ADIC_double_tape_pointer]=var;        \
     __ADIC_double_tape_pointer=__ADIC_double_tape_pointer+1;   \
}

#define pop_s0(var)                                                \
{                                                               \
     __ADIC_double_tape_pointer=__ADIC_double_tape_pointer-1;   \
     var = __ADIC_double_tape[__ADIC_double_tape_pointer];      \
}

#define push_i_s0(var)                                               \
{                                                               \
     __ADIC_integer_tape[__ADIC_integer_tape_pointer]=var;        \
     __ADIC_integer_tape_pointer=__ADIC_integer_tape_pointer+1;   \
}

#define pop_i_s0(var)                                                \
{                                                               \
     __ADIC_integer_tape_pointer=__ADIC_integer_tape_pointer-1;   \
     var = __ADIC_integer_tape[__ADIC_integer_tape_pointer];      \
}

#endif
