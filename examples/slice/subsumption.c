extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume(int);
extern int __VERIFIER_nondet_int();

int main( ) {
  int input = __VERIFIER_nondet_int();
  
  if (input < 3) {
    if (input < 0) {
      __VERIFIER_error();
    }
  } 

  return 0;
}

