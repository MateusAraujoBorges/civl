#include <civlc.cvh>
#include <string.h>

void main(){
    char str[100] = "Hello World!";
    int len = strlen(str);
    
    $assert(len==12);
}
