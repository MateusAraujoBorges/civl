/*
Author: Yihao Yan

Download LCP.zip from: http://fm2012.verifythis.org/challenges

-----------------
Problem decription:

Longest Common Prefix (LCP)
Input:  an integer array X1[n], and two indices x and y into this array
Output: length of the longest common prefix of the subarrays of a
        starting at x and y respectively.
        
-----------------
Verification task:

Implement the lcp function, and verify that it behaves in the way described above.
      
-----------------
Result:

For arrays with length less than 5, lcp function returns an integer n which is
the length of the longest common prefix between its two suffixes: The two suffixes
are the same with indexes from 0 to n-1 while they are different at index n. Therefore
the lcp function behave correctly.

-----------------
command: civl verify lcp.c
*/

#include <civlc.cvh>
#pragma CIVL ACSL
$input int n, x, y;
$assume (0 <= x && x < n && 0 <= y && y < n && 0 < n);
$input int X1[n];

int lcp(int *arr, int n, int x, int y){
  int l = 0;

  /*@ loop invariant 0 <= l && l <= n;
    @ loop invariant 0 <= x + l && x + l <= n;
    @ loop invariant 0 <= y + l && y + l <= n;
    @ loop invariant \forall int i; 0 <= i && i < l ==> arr[x+i]==arr[y+i];
    @ loop assigns l;
    @*/
  while (x+l<n && y+l<n && arr[x+l]==arr[y+l])
      l++;
  return l;
}

void main(){
  int result = lcp(X1, n, x, y);

  $assert($forall (int i: 0 .. result-1) X1[x+i] == X1[y+i]);
  $assert(
	  (x + result < n && y + result < n) => X1[x+result] != X1[y+result]
	  );
}
