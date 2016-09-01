extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume(int);
extern int __VERIFIER_nondet_int();

int main( ) {
  /* Switch on case 1 */
  int input = 1;
  switch (input) {
    case 1:
      break;
    case 2:
      break;
    default:
      __VERIFIER_error();
      break;
  }

  /* Fallthrough */
  switch (input) {
    case 1:
    case 2:
      break;
    default:
      __VERIFIER_error();
      break;
  }

  /* Default */
  input = 5;
  switch (input) {
    case 1:
      break;
    case 2:
      break;
    default:
      __VERIFIER_error();
      break;
  }
  return 0;
}
