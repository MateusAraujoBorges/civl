int x = 0;
int y = 0;
int main() {
  if (x > 0) {
    x++;
  } else if (y > 0) { 
    x--;
  }

  do {
    x++;
  } while (x < 100);

  while (x > 0) {
    x--;
  }

  for (int i=0; i<10; i++) {
    x = x + 1;
  }
}
