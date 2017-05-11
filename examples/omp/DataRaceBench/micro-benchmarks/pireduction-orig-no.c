// Classic PI calculation using reduction    
#define num_steps 2000000000 
    
int main(int argc, char** argv) 
{
  double pi = 0;
  int i;
#pragma omp parallel for reduction(+:pi)
  for (i = 0; i < num_steps; i++) {
    pi += 1.0 / (i * 4.0 + 1.0);
  }
  pi = pi * 4.0;
  return 0;
}

