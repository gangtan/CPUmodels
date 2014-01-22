#include <stdio.h>
#include <stdlib.h>
          
int main(int argc, char **argv)
{

  int a, b, i;
  float c;

  a = atoi(argv[1]);
  b = atoi(argv[2]);
  c = a/b;
  printf("%d/%d = %f \n", a, b, c);
  return 0;

}
