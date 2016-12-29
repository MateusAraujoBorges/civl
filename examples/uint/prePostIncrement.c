$input unsigned int a;

unsigned int f(unsigned int x);

int main(){
  unsigned int k=a, t;

  k++; // should be k=$unsigned_add(k, 1, bound);
  t=f(k++);
  t=f(++k);
}

unsigned int f(unsigned int x){
  return x*2;
}
