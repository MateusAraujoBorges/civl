#include <string.h>

int main() {

  int a[1][1];
  int b[1][1] = {1};

  memcpy(a, &b[0][0], sizeof(int));
  return 0;
}
