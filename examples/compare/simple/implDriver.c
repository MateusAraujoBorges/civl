#include "implDriver.h"

extern int x;
int y = 0;
int a[2];
extern struct TYPE st;

extern int f1();

int main() {
  return x + f1() + a[1] + st.y;
}
