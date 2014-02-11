#include <stdio.h>
#include <stdlib.h>

int main(){

  int count, b;
  unsigned mask;

  union
  {
    float input;
    int output;
  }data;

  float x = 2.5, y = 3.5677;

  data.input =  x + y;

  int nbits = 8 * sizeof(float);


  int m = 0x1 << (nbits -1);

  mask = m;

  for (count = 1; count <= nbits; count++){
    b = (data.output & mask)? 1 : 0;
    printf("%x", b);
  
    if (count % 4 == 0)
       printf(" ");
    mask >>=1; 
  }  

  printf("\n");

  return 0;
}
