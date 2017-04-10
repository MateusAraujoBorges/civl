#include <assert.h>

int main(int argc, char * argv[]) {
  struct point {
    int x;
    int y;
  } point;
  int * test = &point.x + 1;
  assert(test != NULL);
  return 0;
}
