#include <stdio.h>
#include <stdbool.h>
#include <civlc.cvh>

/*
@author: Yihao Yan

Link(challenge 1): http://etaps2015.verifythis.org/challenges

problem description:
Verify a function isRelaxedPrefix determining if a list _pat_ (for
pattern) is a relaxed prefix of another list _a_.

The relaxed prefix property holds iff _pat_ is a prefix of _a_ after
removing at most one element from _pat_.

examples:

pat = {1,3}   is a relaxed prefix of a = {1,3,2,3} (standard prefix)

pat = {1,2,3} is a relaxed prefix of a = {1,3,2,3} (remove 2 from pat)

pat = {1,2,4} is not a relaxed prefix of a = {1,3,2,3}.

command: civl verify RelaxedPrefix_2015_1.c

*/
$input int N1_BOUND = 4;
$input int N2_BOUND = 3;
$input int n1;
$input int n2;
$input int X2[n2];
$input int X1[n1];
$assume (n2>=0 && n2 < N2_BOUND);
$assume (n1>=0 && n1 < N1_BOUND);

bool isRelaxedPrefix(int* pat, int patLen, int* a, int aLen){
  int shift = 0;
  int i;

  if(patLen > aLen+1) return false;

  if(aLen == 0) return true;

  for(i=0; i<patLen; i++){
     if(pat[i] != a[i-shift]){
      if(shift == 0)
        shift = 1;
      else
        return false;
     }
     if(i == aLen - 1 && shift == 0) return true;
   }
  return true;
}

void main(){
	bool result = isRelaxedPrefix(X1, n1, X2, n2);

  if(n1 > n2+1){
    $assert(!result);
  }else if(n1 == n2+1){
    $assert( result ==
      ($exists {int k | k >= 0 && k < n1}
        (
          ($forall {int i | i >= 0 && i < k} X1[i] == X2[i]) &&
          ($forall {int i | i > k && i < n1} X1[i] == X2[i-1])
        )
      )
    );
  }else{
    $assert(result ==
      ($exists {int k | k >= 0 && k <=n1}
        (
          ($forall {int i | i >= 0 && i < k} X1[i] == X2[i]) &&
          ($forall {int i | i > k && i < n1} X1[i] == X2[i-1])
        )
      )
    );
  }
}
