int main(){
  unsigned int t=-2U; // should be translated to (UNSIGNED_MAX+1)-2

  t--;
}
