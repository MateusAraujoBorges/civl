extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume(int);
extern int __VERIFIER_nondet_int();

int main () {

  int input = __VERIFIER_nondet_int();

  if ( (input > 42) || (input < 23) ) {
    int foo1 = 1;
    int foo2 = 2;
  }
  if ( (input < 5) ) {
    while ( (input < 14) ) {
      if (input == 13) {
        __VERIFIER_error();
      }
      input = input + 1;
    }
  } else {
    if ( (input == 33) ) {
     return;
    }
  }
  int foo3 = 3;
}
