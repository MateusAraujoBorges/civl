#include <civlc.cvh>
#include <assert.h>

$input double data[3][3];
$input double A,B,C,D,E,F,G,H,I;
//00 => A
//01 => B
//02 => C
//10 => D
//11 => E
//12 => F
//20 => G
//21 => H
//22 => I

$assume (0==(H * A - 1 * G * B));
$assume (0 == D);
$assume (0 != ((I * A) - (G * C)));
$assume (0 != E &&
	 0 != G &&
	 0 != A);
$assume ((0 == (E * I * A 
		- E * G * C 
		- F * H * A
		+ F * G * B)));

int main() {
  $assert( 1 == 0, "unreachable");
}









