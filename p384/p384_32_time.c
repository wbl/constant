/* Copyright (c) Watson Ladd (Mozilla) 2016 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include <fcntl.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "p384_32.h"

int
main()
{
  /* FIXME: have to deal with scalars that are two large *
   * In NSS use modular arithmetic. Here just set significant part 0 *
   * Which end is big is TBD */
  unsigned char A[96];
  unsigned char B[96];
  unsigned char KAB[96];
  unsigned char KBA[96];
  unsigned char ask[48];
  unsigned char bsk[48];
  int fd;
  fd = open("/dev/urandom", O_RDONLY);
  if (fd < 0) {
    exit(1);
  }
  for (int i = 0; i < 1000; i++) {
    read(fd, ask, 48);
    read(fd, bsk, 48);
    ask[47] = 0;
    bsk[47] = 0;
    p384_32_scalarmult_base(A, ask);
    p384_32_scalarmult_base(B, bsk);
    p384_32_scalarmult(KAB, bsk, A);
    p384_32_scalarmult(KBA, ask, B);
    if (memcmp(KAB, KBA, 96)) {
      printf("Failure to agree \n");
    }
  }
  printf("2000 basepoint mults, 2000 variable mults\n");
}
