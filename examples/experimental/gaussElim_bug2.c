#include <civlc.cvh>
#include <assert.h>

$input double data[3][3];
$input double A,B,C,D,E,F,G,H,I;

/* Unsatisfiable path condition:
   
  0==(X_data[2][1]*X_data[0][0] - 1*X_data[2][0]*X_data[0][1])
  0==X_data[1][0]
  (X__gen_argc-9)<=0
  0<=(SIZEOF(388)-1)
  0<=(SIZEOF_INT-1)
  0<=(SIZEOF_REAL-1)
  0<=(X__gen_argc-1)
  0!=((X_data[2][2]*X_data[0][0])+(-1*(X_data[2][0]*X_data[0][2])))
  0!=X_data[1][1]
  0!=X_data[2][0]
  0!=X_data[0][0]
  (0==(X_data[1][1]*X_data[2][2]*X_data[0][0] - 1*X_data[1][1]*X_data[2][0]*X_data[0][2] - 1*X_data[1][2]*X_data[2][1]*X_data[0][0] + X_data[1][2]*X_data[2][0]*X_data[0][1]))||(0==X_data[0][0])

*/

$assume (0 == (data[2][1] * data[0][0] - data[2][0] * data[0][1]));
$assume (0 == data[1][0]);
$assume (0 != ((data[2][2] * data[0][0]) - (data[2][0] * data[0][2])));
$assume (0 != data[1][1] &&
	 0 != data[2][0] &&
	 0 != data[0][0]);
$assume ((0 == (data[1][1] * data[2][2] * data[0][0] 
		- data[1][1] * data[2][0] * data[0][2] 
		- data[1][2] * data[2][1] * data[0][0]
		+ data[1][2] * data[2][0] * data[0][1]))
	 || (data[0][0] == 0));

int main() {
  $assert( 1 == 0, "unreachable");
}










