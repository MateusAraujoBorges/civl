#include <stdio.h>
#include <assert.h>

int main(int argc, char * argv[]) {
  int a[3];
  int *p = a + 100;

  assert(p);
}

