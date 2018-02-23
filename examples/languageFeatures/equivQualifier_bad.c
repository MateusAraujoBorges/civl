#include <civlc.cvh>
#include <pointer.cvh>

$input double ARR1[3];

void main() {
    double ARR2[3];
    
    for (int i = 0; i < 3; i ++) {
        ARR2[i] = ARR1[i]+1;
    }
    $assert($equals(&ARR2, &ARR1));
}
