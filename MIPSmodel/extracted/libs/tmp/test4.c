#include <stdio.h>
#include <limits.h>

int main(void) {
  int i, j;
  float f, *pf;
  char *pc;

  f = 15; /* assign some arbitrary value */
  pf = &f;
  pc = (char *)pf;

  for (i = 0; i < sizeof(float); i++) {
    for (j = 0; j < CHAR_BIT; j++) {
      printf("%d", *pc & (1 << j) ? 1 : 0);
      fflush(stdout);
    }
    pc++;
    printf(" ");
    fflush(stdout);
  }

  return 0;
}
