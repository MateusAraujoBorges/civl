#include "typedefbugHeader.h"

typedef struct v_t {
  int val;
} V;

int getVal(V *v) {
  return v->val;
}

int main() {
	V v0;
	
	return v0.val;
}

