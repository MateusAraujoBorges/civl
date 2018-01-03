#include "typedefbugHeader.h"

typedef struct v_t {
  int val;
} V;

int getVal(V *v) {
  return v->val;
}

