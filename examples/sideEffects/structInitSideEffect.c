struct Node{
  int x;
  int y;
  int z;
};

int f(int a){
  return a;
}

int main(){
  struct Node node = {f(0), f(1), f(2)};
  return 0;
}

