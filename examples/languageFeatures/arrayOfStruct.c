int main() {
  struct {
    int a;
    int b;
    struct {
      int x;
      int y;
    } c;
  } c[10];

  int d = c[0].a + c[1].b + c[0].c.x + c[1].c.y;
  return d;
}
