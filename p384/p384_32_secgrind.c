#include <stdbool.h>
#include "p384_32.h"
int main(){
  unsigned char p[96];
  unsigned char q[96];
  unsigned char s1[48];
  unsigned char s2[48];
  p384_32_scalarmult_base(p, s1);
  p384_32_scalarmult(q, s2, p);
}
