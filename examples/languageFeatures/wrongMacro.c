/* This file is suppose to show a buggy crash in CIVL when                                                                        
 * the user provides an undefined macro value.                                                                                    
 * For example:                                                                                                                   
 *  civl verify -DMAC=mac_ooo wrongMacro.c                                                                                        
 */
#include <assert.h>
#ifndef MAC
#define MAC mac_zero
#endif

enum mac_numbers { mac_zero = 0, mac_one, mac_two};


int main() {
  enum mac_numbers mn = MAC;

  if (mn == mac_one)
    assert(mn == 1);
  if (mn == mac_two)
    assert(mn == 2);
  return 0;
}
