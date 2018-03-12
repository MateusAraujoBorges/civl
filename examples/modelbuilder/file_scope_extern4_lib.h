//typedef struct type Type;

enum SubEnum {one, two};

typedef struct subtype {
  enum SubEnum w;
  double z;
} SubType;

typedef struct type {
 SubType x;
 int y;
} Type;

int value(Type t);
