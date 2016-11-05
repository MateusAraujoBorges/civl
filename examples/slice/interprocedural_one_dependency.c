extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume(int);
extern int __VERIFIER_nondet_int();

int g (int in) {
  if (in > 2) {
    __VERIFIER_error();
  } 
}

int main () {

  int input = __VERIFIER_nondet_int();

  if ( (input > 0 && input < 4) ) {
    g(input-10);
  } else {
    g(input-10);
  }
  g(input);

}
