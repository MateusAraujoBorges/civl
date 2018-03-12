#include "file_scope_extern3_lib.h"

enum SubEnum {one, two};

typedef struct subtype {
  enum SubEnum d;
  double z;
} SubType;

typedef struct type {
 SubType x;
 int y;
} Type;

Type t = {{0, 0.}, 9};

int value(Type t) { return t.y;}
