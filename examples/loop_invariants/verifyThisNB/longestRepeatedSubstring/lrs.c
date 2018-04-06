/*
Author: Yihao Yan

Download LCP.zip from: http://fm2012.verifythis.org/challenges

-----------------
Problem background:

Together with a suffix array, LCP can be used to solve interesting text
problems, such as finding the longest repeated substring (LRS) in a text.

A suffix array (for a given text) is an array of all suffixes of the
text. For the text [7,8,8,6], the suffix array is
[[7,8,8,6],
   [8,8,6],
     [8,6],
       [6]]

Typically, the suffixes are not stored explicitly as above but
represented as pointers into the original text. The suffixes in a suffix
array  are sorted in lexicographical order. This way, occurrences of
repeated substrings in the original text are neighbors in the suffix
array. 

-----------------
Verification task:

Implement longest repeated substring function and verify that it does so correctly.

-----------------                                                                                                                                                                 
Result:

For all strings with length less than 5, the lrs function returns an index i and a length l.
The verification shows that the sub string with length l starting from index i is repeated in 
the original string and also, there exists no repeated string with length greater than l. Therefore
the implemented function lrs behaves correctly. 

-----------------  
command: minor changes
*/

#include <stdlib.h>
#include <civlc.cvh>
#include <assert.h>

#pragma CIVL ACSL

$input int N;
$assume(N > 0);
$input int X1[N];

#define GT(x,y,arr) (\exists int t; 0 <= t && t < n && (x) + t < n && (y) + t <= n \
		     &&  (y + t == n || (arr)[(x)+t] > (arr)[(y)+t]) \
		     (\forall int k; 0 <= k && k < t ==> (arr)[(x)+k] == (arr)[(y)+k]) && \
		     )

int lcp1(int *arr, int n, int x, int y) {
  int l = 0;

  /*@ loop invariant 0 <= l && l <= n;
    @ loop invariant 0 <= x + l && x + l <= n;
    @ loop invariant 0 <= y + l && y + l <= n;
    @ loop invariant \forall int i; 0 <= i && i < l ==> arr[x+i]==arr[y+i];
    @ loop assigns l;
    @*/
  while (x+l<n && y+l<n && arr[x+l]==arr[y+l]) {
      l++;
  }
  return l;
}

/* returns:
 *   0 if x and y points to the same suffix;
 *   poistive value if x "is greater than" y;
 *   negative value if x "is NO greater than" y;
 */
int compare(int *a, int n, int x, int y) {
    if (x == y) return 0;

    int l = lcp1(a, n, x, y);

    if (x+l == n) return -1;
    if (y+l == n) return 1;
    if (a[x+l] < a[y+l]) return -1;
    if (a[x+l] > a[y+l]) return 1;
    return -2;
}

void sort(int *a, int n, int *data) {
  for(int i = 1; i < n; i++) {
    int comp = compare(a, n, data[i - 1], data[i]);

    /*@ loop invariant 0 <= j && j <= i;
      @ loop invariant \forall int k; j < k && k <= i ==> GT(k-1,k,data);
      @ loop assigns j, comp, data[j-1 .. j];
      @*/
    for(int j = i; j > 0 && comp > 0;) {
      // swap:
      int tmp = data[j];
      
      data[j] = data[j-1];
      data[j-1] = tmp;
      j--;
      if (j > 0)
	comp = compare(a, n, data[j - 1], data[j]);
    }
  }
}

int lcp2(int *a, int n, int index, int* suffixes) {
    return lcp1(a,n,suffixes[index], suffixes[index-1]);
}

/**
result[0]: index
result[1]: length
*/
void lrs(int* a, int n, int *result) {
  int suffixes[n];

  for(int i=0; i<n; i++) {
    suffixes[i] = i;
  }
  sort(a, n, suffixes);
  for(int i=1; i<n; i++) {
    int len = lcp2(a, n, i,suffixes);

    if(len > result[1]) {
      result[0] = suffixes[i];
      result[1] = len;
    }
  }
}

int main(){
  int* result = (int*)malloc(2* sizeof(int));

  result[0] = 0;
  result[1] = 0;
  lrs(X1, N, result);

  int index = result[0];
  int maxLen = result[1];

  if(N > 1) {
    $assert($exists (int k | k >= 0 && k <= N - maxLen && k != index)
	    ($forall (int i: 0 .. maxLen-1) X1[k+i] == X1[index+i])
	    );
    $assert(!($exists (int k | k >= 0 && k <= N - maxLen - 1)
	      ($exists (int j | j >= 0 && j <= N - maxLen - 1 && j != k)
	       ($forall (int i: 0 .. maxLen) X1[k+i] == X1[j+i])
	       )
	      )
	    );
  }else{
    $assert(index == 0 && maxLen == 0);
  }

  free(result);
  return 0;
}
