#include <civlc.cvh>

void main(){
    int a = 2;
    int b = 3;
    int arr[6];
    
    for(int i = 0; i <= a+b; i++) {
        arr[i] = 1;
    }
    $assert($forall (int k: 0 .. (a+b)) arr[k]==1);
}
