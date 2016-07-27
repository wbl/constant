#include <fcntl.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "p384_64.h"

int
main()
{
  /* FIXME: have to deal with scalars that are two large *
   * In NSS use modular arithmetic. Here just set significant part 0 *
   * Which end is big is TBD */
  unsigned char P[96];
  unsigned char Q[96];
  unsigned char ask[48];
  unsigned char bsk[48];
  int fd;
  fd = open("/dev/urandom", O_RDONLY);
  if (fd < 0) {
    exit(1);
  }
   read(fd, ask, 48);
   read(fd, bsk, 48);
   ask[47]=0;
   bsk[47]=0;
   p384_64_scalarmult_base(Q, ask);
   for (int i = 0; i < 5000; i++) {
     p384_64_double_scalarmult_base(P, Q, ask, bsk);
   }
  printf("5000 double scalarmults\n");
}
