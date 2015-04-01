//given b, satisfy a * (a + b) = c * c, maximize a.

#include <stdio.h>
#include <stdlib.h>
#include <math.h>

int main() {
  int b, w;
  while(scanf("%d", &b) != EOF) {
    w = 1;
    while(!(b & 1)) {
      w *= 2;
      b /= 2;
    }
    int n = (b * b + 1) / 2 * w;
    b *= w;
    int a = (n - b) / 2;
    int c2 = a * (a + b);
    int c = sqrt(c2);
    printf("%d %d %d\n", a, c2, c * c);

  }
  return 0;
}
