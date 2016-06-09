$input int x;
int s=0;

void foo(){
  $when(s>0);
  $atomic{
    s--;
  }
}

void goo(){
  $atomic{
    s=1;
    $when(x>0)
      s*=2;
  }
}

int main(){
  $proc fp, gp;
  
  $atomic{
    fp = $spawn foo();
    gp = $spawn goo();
  }
  $wait(fp);
  $wait(gp);
}
