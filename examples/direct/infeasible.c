#include <civlc.cvh>

int not_true = 0;
int main() {
  if (not_true) {
    $assert(0);
  }
}
