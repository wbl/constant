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
  /* FIXME: have to deal with scalars that are too large *
   * In NSS use modular arithmetic. Here just set significant part 0 *
   * Which end is big is TBD */
  unsigned char A[96];
  unsigned char B[96];
  unsigned char KAB[96];
  unsigned char KBA[96];
  unsigned char ask[48];
  unsigned char bsk[48];
  unsigned char basepoint[96];
  unsigned char result[96];
  int fd;
  fd = open("/dev/urandom", O_RDONLY);
  if (fd < 0) {
    exit(1);
  }
  for (int i = 0; i < 48; i++) {
    ask[i] = 0;
  }
  for (int i = 1; i < 21; i++) {
    ask[0] = i;
    printf("k = %u\n", i);
    p384_32_scalarmult_base(A, ask);
    if(!p384_32_valid(A)){
      printf("Validity issue!\n");
    }
    printf("x = ");
    for (int i = 0; i < 48; i++) {
      printf("%02x", A[i]);
    }
    printf("\n");
    printf("y = ");
    for (int i = 0; i < 48; i++) {
      printf("%02x", A[i + 48]);
    }
    printf("\n\n");
  }

  for(int i=0; i<48; i++){
    ask[i]=0;
  }
  read(fd, bsk, 48);
  bsk[47] = 0;
  p384_32_scalarmult_base(B, bsk);
  p384_32_scalarmult(A, ask, B);
  int flag = 0;
  for(int i=0; i<96; i++){
    if(A[i]){
      flag = 1;
    }
  }
  if(flag){
    printf("failure to properly compute point at infinity!\n");
  }
  for (int i = 0; i < 100; i++) {
    read(fd, ask, 48);
    read(fd, bsk, 48);
    ask[47] = 0;
    bsk[47] = 0;
    p384_32_scalarmult_base(A, ask);
    p384_32_scalarmult_base(B, bsk);
    if(!p384_32_valid(A) || !p384_32_valid(B)){
      printf("Validity issue!\n");
    }
    p384_32_scalarmult(KAB, bsk, A);
    p384_32_scalarmult(KBA, ask, B);
    if (memcmp(KAB, KBA, 96)) {
      printf("Failure to agree \n");
    }
  }
  // Now test the doublescalarmult
  for(int i=0; i<48; i++){
    ask[i]=0;
    bsk[i]=0;
  }
  //We do a test that Q=n1*base+n2*base is same if n1+n2 is a constant
  ask[0]=1;
  p384_32_scalarmult_base(basepoint, ask);
  ask[0]=255;
  ask[1]=255;
  p384_32_scalarmult_base(result, ask);
  for(int i=0; i<=255; i++){
    ask[0]=i;
    ask[1]=255-i;
    bsk[0]=255-i;
    bsk[1]=i;
    p384_32_double_scalarmult_base(B, basepoint, ask, bsk);
    if(memcmp(B, result, 96)){
      printf("Doublemult failure with %i and %i\n", ask[0], bsk[0]);
    }
  }
  ask[0]=0;
  ask[1]=1;
  p384_32_scalarmult_base(result, ask);
  ask[0]=250;
  bsk[0]=6;
  ask[1]=0;
  bsk[1]=0;
  p384_32_double_scalarmult_base(B, basepoint, ask, bsk);
  if(memcmp(B, result, 96)){
    printf("Doublemult failure on carry!\n");
  }
}
