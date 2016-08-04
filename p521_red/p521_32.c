#include <assert.h>
#include <fcntl.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <unistd.h>

#include "p521_32.h"
/* Copyright (c) Watson Ladd (Mozilla) 2016 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

/* A 32 bit constant time implementation of P521.*/
/* 19 28 bit words */

/* Constants */
typedef uint32_t felem[19];

static const felem prime = {
    0xfffffff, 0xfffffff, 0xfffffff, 0xfffffff, 0xfffffff, 0xfffffff, 0xfffffff,
    0xfffffff, 0xfffffff, 0xfffffff, 0xfffffff, 0xfffffff, 0xfffffff, 0xfffffff,
    0xfffffff, 0xfffffff, 0xfffffff, 0xfffffff, 0x1ffff};

static const felem base_x = {
    0x2e5bd66, 0x7e7e31c, 0xa429bf9, 0xb3c1856, 0x8de3348, 0x27a2ffa, 0x8fe1dc1,
    0xefe7592, 0x14b5e77, 0x4d3dbaa, 0x8af606b, 0xb521f82, 0x139053f, 0x429c648,
    0x62395b4, 0x9e3ecb6, 0x404e9cd, 0x8e06b70, 0xc685};

static const felem base_y = {
    0xfd16650, 0xbe94769, 0x2c24088, 0x7086a27, 0x761353c, 0x13fad0,  0xc550b9,
    0x5ef4264, 0x7ee7299, 0x3e662c9, 0xfbd1727, 0x446817a, 0x449579b, 0xd998f54,
    0x42c7d1b, 0x5c8a5fb, 0xa3bc004, 0x296a789, 0x11839};

static const uint32_t bottom28 = 0x0fffffff;
static const uint32_t topmask = (1 << 17) - 1;
/* Debugging functions */
static void printelem(char *name, const felem a) {
  printf("%s = 0 ", name);
  for (int i = 0; i < 19; i++) {
    printf("+ 2**(28*%d)*%u", i, a[i]);
  }
  printf("\n");
}

static bool is_fully_reduced(const felem a) {
  int flag = 1;
  for (int i = 0; i < 19; i++) {
    flag &= (a[i] <= bottom28);
  }
  flag &= (a[18] <= prime[18]);
  return flag;
}

/* Field Arithmetic */
static void reduce_carry(felem a) {
  /* Preconditions: a[i]<2^28, a[18]<2^28*/
  /* Postconditions a%p unchanged, a[i]<2^29, a<p+1 */
  uint32_t carry = a[18] >> 17;
  a[18] &= topmask;
  a[0] += carry; // 2^521=2 mod p
}

static void carry_prop(felem a) { /* moves carries down, lets a[18] grow */
  /* pre: a[i]<2^31 */
  /* post: a[i]<2^28 */
  uint32_t carry = 0;
  for (int i = 0; i < 18; i++) {
    carry += a[i];
    a[i] = carry & bottom28;
    carry = carry >> 28;
  }
  a[18] += carry;
}

static void reduce_total(felem a) {
  //  printelem("red_in", a);
  // printelem("prime", prime);
  felem d;
  uint32_t mask;
  carry_prop(a);   // shrink limbs
  reduce_carry(a); // a<p+1
  carry_prop(a);
  reduce_carry(a);
  for (int i = 0; i < 19; i++) {
    d[i] = a[i];
  }
  d[0] += 1;          // add 1
  carry_prop(d);      // propagate
  mask = d[18] >> 17; // we've now subtracted p, and mask tells us if we need to
  d[18] &= topmask;
  mask = -mask;
  for (int i = 0; i < 19; i++) {
    a[i] ^= (a[i] ^ d[i]) & mask; // conditional swap
  }
  assert(is_fully_reduced(a));
  // printelem("red_out", a);
  // printf("print 'red_res', (red_in %% prime) == (red_out %% prime)\n");
}

static void mostly_reduce(felem a) {
  carry_prop(a);
  reduce_carry(a);
}

static void add(felem r, const felem a,
                const felem b) { /*Precondition: a[i] and b[i] <2^r, r<30*/
  /*Postcondition: r[i] < 2^(r+1) */
  /* In practice result will need to be 29 bits, and so input 28 bits */
  for (int i = 0; i < 19; i++) {
    r[i] = a[i] + b[i];
  }
}

static void sub(felem r, const felem a, const felem b) {
  /* Preconditions: each element of b[i]<2^28, b < 4*p, a[i]<2^29 */
  /* Postconditions: r[i]<2^29, r<2p*/
  for (int i = 0; i < 19; i++) {
    r[i] = a[i] + (4 * prime[i] - b[i]);
  }
  mostly_reduce(r);
}

static void mult_nored(uint64_t r[38], const felem a, const felem b) {
  /* Precondition: a[i]<2^29, b[i]<2^29 */
  /* Postcondition r[i]<19*2^58<2^63*/
  r[0] = 0 + ((uint64_t)a[0]) * b[0];

  r[1] = 0 + ((uint64_t)a[0]) * b[1] + ((uint64_t)a[1]) * b[0];

  r[2] = 0 + ((uint64_t)a[0]) * b[2] + ((uint64_t)a[1]) * b[1] +
         ((uint64_t)a[2]) * b[0];

  r[3] = 0 + ((uint64_t)a[0]) * b[3] + ((uint64_t)a[1]) * b[2] +
         ((uint64_t)a[2]) * b[1] + ((uint64_t)a[3]) * b[0];

  r[4] = 0 + ((uint64_t)a[0]) * b[4] + ((uint64_t)a[1]) * b[3] +
         ((uint64_t)a[2]) * b[2] + ((uint64_t)a[3]) * b[1] +
         ((uint64_t)a[4]) * b[0];

  r[5] = 0 + ((uint64_t)a[0]) * b[5] + ((uint64_t)a[1]) * b[4] +
         ((uint64_t)a[2]) * b[3] + ((uint64_t)a[3]) * b[2] +
         ((uint64_t)a[4]) * b[1] + ((uint64_t)a[5]) * b[0];

  r[6] = 0 + ((uint64_t)a[0]) * b[6] + ((uint64_t)a[1]) * b[5] +
         ((uint64_t)a[2]) * b[4] + ((uint64_t)a[3]) * b[3] +
         ((uint64_t)a[4]) * b[2] + ((uint64_t)a[5]) * b[1] +
         ((uint64_t)a[6]) * b[0];

  r[7] = 0 + ((uint64_t)a[0]) * b[7] + ((uint64_t)a[1]) * b[6] +
         ((uint64_t)a[2]) * b[5] + ((uint64_t)a[3]) * b[4] +
         ((uint64_t)a[4]) * b[3] + ((uint64_t)a[5]) * b[2] +
         ((uint64_t)a[6]) * b[1] + ((uint64_t)a[7]) * b[0];

  r[8] = 0 + ((uint64_t)a[0]) * b[8] + ((uint64_t)a[1]) * b[7] +
         ((uint64_t)a[2]) * b[6] + ((uint64_t)a[3]) * b[5] +
         ((uint64_t)a[4]) * b[4] + ((uint64_t)a[5]) * b[3] +
         ((uint64_t)a[6]) * b[2] + ((uint64_t)a[7]) * b[1] +
         ((uint64_t)a[8]) * b[0];

  r[9] = 0 + ((uint64_t)a[0]) * b[9] + ((uint64_t)a[1]) * b[8] +
         ((uint64_t)a[2]) * b[7] + ((uint64_t)a[3]) * b[6] +
         ((uint64_t)a[4]) * b[5] + ((uint64_t)a[5]) * b[4] +
         ((uint64_t)a[6]) * b[3] + ((uint64_t)a[7]) * b[2] +
         ((uint64_t)a[8]) * b[1] + ((uint64_t)a[9]) * b[0];

  r[10] = 0 + ((uint64_t)a[0]) * b[10] + ((uint64_t)a[1]) * b[9] +
          ((uint64_t)a[2]) * b[8] + ((uint64_t)a[3]) * b[7] +
          ((uint64_t)a[4]) * b[6] + ((uint64_t)a[5]) * b[5] +
          ((uint64_t)a[6]) * b[4] + ((uint64_t)a[7]) * b[3] +
          ((uint64_t)a[8]) * b[2] + ((uint64_t)a[9]) * b[1] +
          ((uint64_t)a[10]) * b[0];

  r[11] = 0 + ((uint64_t)a[0]) * b[11] + ((uint64_t)a[1]) * b[10] +
          ((uint64_t)a[2]) * b[9] + ((uint64_t)a[3]) * b[8] +
          ((uint64_t)a[4]) * b[7] + ((uint64_t)a[5]) * b[6] +
          ((uint64_t)a[6]) * b[5] + ((uint64_t)a[7]) * b[4] +
          ((uint64_t)a[8]) * b[3] + ((uint64_t)a[9]) * b[2] +
          ((uint64_t)a[10]) * b[1] + ((uint64_t)a[11]) * b[0];

  r[12] = 0 + ((uint64_t)a[0]) * b[12] + ((uint64_t)a[1]) * b[11] +
          ((uint64_t)a[2]) * b[10] + ((uint64_t)a[3]) * b[9] +
          ((uint64_t)a[4]) * b[8] + ((uint64_t)a[5]) * b[7] +
          ((uint64_t)a[6]) * b[6] + ((uint64_t)a[7]) * b[5] +
          ((uint64_t)a[8]) * b[4] + ((uint64_t)a[9]) * b[3] +
          ((uint64_t)a[10]) * b[2] + ((uint64_t)a[11]) * b[1] +
          ((uint64_t)a[12]) * b[0];

  r[13] = 0 + ((uint64_t)a[0]) * b[13] + ((uint64_t)a[1]) * b[12] +
          ((uint64_t)a[2]) * b[11] + ((uint64_t)a[3]) * b[10] +
          ((uint64_t)a[4]) * b[9] + ((uint64_t)a[5]) * b[8] +
          ((uint64_t)a[6]) * b[7] + ((uint64_t)a[7]) * b[6] +
          ((uint64_t)a[8]) * b[5] + ((uint64_t)a[9]) * b[4] +
          ((uint64_t)a[10]) * b[3] + ((uint64_t)a[11]) * b[2] +
          ((uint64_t)a[12]) * b[1] + ((uint64_t)a[13]) * b[0];

  r[14] = 0 + ((uint64_t)a[0]) * b[14] + ((uint64_t)a[1]) * b[13] +
          ((uint64_t)a[2]) * b[12] + ((uint64_t)a[3]) * b[11] +
          ((uint64_t)a[4]) * b[10] + ((uint64_t)a[5]) * b[9] +
          ((uint64_t)a[6]) * b[8] + ((uint64_t)a[7]) * b[7] +
          ((uint64_t)a[8]) * b[6] + ((uint64_t)a[9]) * b[5] +
          ((uint64_t)a[10]) * b[4] + ((uint64_t)a[11]) * b[3] +
          ((uint64_t)a[12]) * b[2] + ((uint64_t)a[13]) * b[1] +
          ((uint64_t)a[14]) * b[0];

  r[15] = 0 + ((uint64_t)a[0]) * b[15] + ((uint64_t)a[1]) * b[14] +
          ((uint64_t)a[2]) * b[13] + ((uint64_t)a[3]) * b[12] +
          ((uint64_t)a[4]) * b[11] + ((uint64_t)a[5]) * b[10] +
          ((uint64_t)a[6]) * b[9] + ((uint64_t)a[7]) * b[8] +
          ((uint64_t)a[8]) * b[7] + ((uint64_t)a[9]) * b[6] +
          ((uint64_t)a[10]) * b[5] + ((uint64_t)a[11]) * b[4] +
          ((uint64_t)a[12]) * b[3] + ((uint64_t)a[13]) * b[2] +
          ((uint64_t)a[14]) * b[1] + ((uint64_t)a[15]) * b[0];

  r[16] = 0 + ((uint64_t)a[0]) * b[16] + ((uint64_t)a[1]) * b[15] +
          ((uint64_t)a[2]) * b[14] + ((uint64_t)a[3]) * b[13] +
          ((uint64_t)a[4]) * b[12] + ((uint64_t)a[5]) * b[11] +
          ((uint64_t)a[6]) * b[10] + ((uint64_t)a[7]) * b[9] +
          ((uint64_t)a[8]) * b[8] + ((uint64_t)a[9]) * b[7] +
          ((uint64_t)a[10]) * b[6] + ((uint64_t)a[11]) * b[5] +
          ((uint64_t)a[12]) * b[4] + ((uint64_t)a[13]) * b[3] +
          ((uint64_t)a[14]) * b[2] + ((uint64_t)a[15]) * b[1] +
          ((uint64_t)a[16]) * b[0];

  r[17] = 0 + ((uint64_t)a[0]) * b[17] + ((uint64_t)a[1]) * b[16] +
          ((uint64_t)a[2]) * b[15] + ((uint64_t)a[3]) * b[14] +
          ((uint64_t)a[4]) * b[13] + ((uint64_t)a[5]) * b[12] +
          ((uint64_t)a[6]) * b[11] + ((uint64_t)a[7]) * b[10] +
          ((uint64_t)a[8]) * b[9] + ((uint64_t)a[9]) * b[8] +
          ((uint64_t)a[10]) * b[7] + ((uint64_t)a[11]) * b[6] +
          ((uint64_t)a[12]) * b[5] + ((uint64_t)a[13]) * b[4] +
          ((uint64_t)a[14]) * b[3] + ((uint64_t)a[15]) * b[2] +
          ((uint64_t)a[16]) * b[1] + ((uint64_t)a[17]) * b[0];

  r[18] = 0 + ((uint64_t)a[0]) * b[18] + ((uint64_t)a[1]) * b[17] +
          ((uint64_t)a[2]) * b[16] + ((uint64_t)a[3]) * b[15] +
          ((uint64_t)a[4]) * b[14] + ((uint64_t)a[5]) * b[13] +
          ((uint64_t)a[6]) * b[12] + ((uint64_t)a[7]) * b[11] +
          ((uint64_t)a[8]) * b[10] + ((uint64_t)a[9]) * b[9] +
          ((uint64_t)a[10]) * b[8] + ((uint64_t)a[11]) * b[7] +
          ((uint64_t)a[12]) * b[6] + ((uint64_t)a[13]) * b[5] +
          ((uint64_t)a[14]) * b[4] + ((uint64_t)a[15]) * b[3] +
          ((uint64_t)a[16]) * b[2] + ((uint64_t)a[17]) * b[1] +
          ((uint64_t)a[18]) * b[0];

  r[19] = 0 + ((uint64_t)a[1]) * b[18] + ((uint64_t)a[2]) * b[17] +
          ((uint64_t)a[3]) * b[16] + ((uint64_t)a[4]) * b[15] +
          ((uint64_t)a[5]) * b[14] + ((uint64_t)a[6]) * b[13] +
          ((uint64_t)a[7]) * b[12] + ((uint64_t)a[8]) * b[11] +
          ((uint64_t)a[9]) * b[10] + ((uint64_t)a[10]) * b[9] +
          ((uint64_t)a[11]) * b[8] + ((uint64_t)a[12]) * b[7] +
          ((uint64_t)a[13]) * b[6] + ((uint64_t)a[14]) * b[5] +
          ((uint64_t)a[15]) * b[4] + ((uint64_t)a[16]) * b[3] +
          ((uint64_t)a[17]) * b[2] + ((uint64_t)a[18]) * b[1];

  r[20] = 0 + ((uint64_t)a[2]) * b[18] + ((uint64_t)a[3]) * b[17] +
          ((uint64_t)a[4]) * b[16] + ((uint64_t)a[5]) * b[15] +
          ((uint64_t)a[6]) * b[14] + ((uint64_t)a[7]) * b[13] +
          ((uint64_t)a[8]) * b[12] + ((uint64_t)a[9]) * b[11] +
          ((uint64_t)a[10]) * b[10] + ((uint64_t)a[11]) * b[9] +
          ((uint64_t)a[12]) * b[8] + ((uint64_t)a[13]) * b[7] +
          ((uint64_t)a[14]) * b[6] + ((uint64_t)a[15]) * b[5] +
          ((uint64_t)a[16]) * b[4] + ((uint64_t)a[17]) * b[3] +
          ((uint64_t)a[18]) * b[2];

  r[21] = 0 + ((uint64_t)a[3]) * b[18] + ((uint64_t)a[4]) * b[17] +
          ((uint64_t)a[5]) * b[16] + ((uint64_t)a[6]) * b[15] +
          ((uint64_t)a[7]) * b[14] + ((uint64_t)a[8]) * b[13] +
          ((uint64_t)a[9]) * b[12] + ((uint64_t)a[10]) * b[11] +
          ((uint64_t)a[11]) * b[10] + ((uint64_t)a[12]) * b[9] +
          ((uint64_t)a[13]) * b[8] + ((uint64_t)a[14]) * b[7] +
          ((uint64_t)a[15]) * b[6] + ((uint64_t)a[16]) * b[5] +
          ((uint64_t)a[17]) * b[4] + ((uint64_t)a[18]) * b[3];

  r[22] = 0 + ((uint64_t)a[4]) * b[18] + ((uint64_t)a[5]) * b[17] +
          ((uint64_t)a[6]) * b[16] + ((uint64_t)a[7]) * b[15] +
          ((uint64_t)a[8]) * b[14] + ((uint64_t)a[9]) * b[13] +
          ((uint64_t)a[10]) * b[12] + ((uint64_t)a[11]) * b[11] +
          ((uint64_t)a[12]) * b[10] + ((uint64_t)a[13]) * b[9] +
          ((uint64_t)a[14]) * b[8] + ((uint64_t)a[15]) * b[7] +
          ((uint64_t)a[16]) * b[6] + ((uint64_t)a[17]) * b[5] +
          ((uint64_t)a[18]) * b[4];

  r[23] = 0 + ((uint64_t)a[5]) * b[18] + ((uint64_t)a[6]) * b[17] +
          ((uint64_t)a[7]) * b[16] + ((uint64_t)a[8]) * b[15] +
          ((uint64_t)a[9]) * b[14] + ((uint64_t)a[10]) * b[13] +
          ((uint64_t)a[11]) * b[12] + ((uint64_t)a[12]) * b[11] +
          ((uint64_t)a[13]) * b[10] + ((uint64_t)a[14]) * b[9] +
          ((uint64_t)a[15]) * b[8] + ((uint64_t)a[16]) * b[7] +
          ((uint64_t)a[17]) * b[6] + ((uint64_t)a[18]) * b[5];

  r[24] = 0 + ((uint64_t)a[6]) * b[18] + ((uint64_t)a[7]) * b[17] +
          ((uint64_t)a[8]) * b[16] + ((uint64_t)a[9]) * b[15] +
          ((uint64_t)a[10]) * b[14] + ((uint64_t)a[11]) * b[13] +
          ((uint64_t)a[12]) * b[12] + ((uint64_t)a[13]) * b[11] +
          ((uint64_t)a[14]) * b[10] + ((uint64_t)a[15]) * b[9] +
          ((uint64_t)a[16]) * b[8] + ((uint64_t)a[17]) * b[7] +
          ((uint64_t)a[18]) * b[6];

  r[25] = 0 + ((uint64_t)a[7]) * b[18] + ((uint64_t)a[8]) * b[17] +
          ((uint64_t)a[9]) * b[16] + ((uint64_t)a[10]) * b[15] +
          ((uint64_t)a[11]) * b[14] + ((uint64_t)a[12]) * b[13] +
          ((uint64_t)a[13]) * b[12] + ((uint64_t)a[14]) * b[11] +
          ((uint64_t)a[15]) * b[10] + ((uint64_t)a[16]) * b[9] +
          ((uint64_t)a[17]) * b[8] + ((uint64_t)a[18]) * b[7];

  r[26] = 0 + ((uint64_t)a[8]) * b[18] + ((uint64_t)a[9]) * b[17] +
          ((uint64_t)a[10]) * b[16] + ((uint64_t)a[11]) * b[15] +
          ((uint64_t)a[12]) * b[14] + ((uint64_t)a[13]) * b[13] +
          ((uint64_t)a[14]) * b[12] + ((uint64_t)a[15]) * b[11] +
          ((uint64_t)a[16]) * b[10] + ((uint64_t)a[17]) * b[9] +
          ((uint64_t)a[18]) * b[8];

  r[27] = 0 + ((uint64_t)a[9]) * b[18] + ((uint64_t)a[10]) * b[17] +
          ((uint64_t)a[11]) * b[16] + ((uint64_t)a[12]) * b[15] +
          ((uint64_t)a[13]) * b[14] + ((uint64_t)a[14]) * b[13] +
          ((uint64_t)a[15]) * b[12] + ((uint64_t)a[16]) * b[11] +
          ((uint64_t)a[17]) * b[10] + ((uint64_t)a[18]) * b[9];

  r[28] = 0 + ((uint64_t)a[10]) * b[18] + ((uint64_t)a[11]) * b[17] +
          ((uint64_t)a[12]) * b[16] + ((uint64_t)a[13]) * b[15] +
          ((uint64_t)a[14]) * b[14] + ((uint64_t)a[15]) * b[13] +
          ((uint64_t)a[16]) * b[12] + ((uint64_t)a[17]) * b[11] +
          ((uint64_t)a[18]) * b[10];

  r[29] = 0 + ((uint64_t)a[11]) * b[18] + ((uint64_t)a[12]) * b[17] +
          ((uint64_t)a[13]) * b[16] + ((uint64_t)a[14]) * b[15] +
          ((uint64_t)a[15]) * b[14] + ((uint64_t)a[16]) * b[13] +
          ((uint64_t)a[17]) * b[12] + ((uint64_t)a[18]) * b[11];

  r[30] = 0 + ((uint64_t)a[12]) * b[18] + ((uint64_t)a[13]) * b[17] +
          ((uint64_t)a[14]) * b[16] + ((uint64_t)a[15]) * b[15] +
          ((uint64_t)a[16]) * b[14] + ((uint64_t)a[17]) * b[13] +
          ((uint64_t)a[18]) * b[12];

  r[31] = 0 + ((uint64_t)a[13]) * b[18] + ((uint64_t)a[14]) * b[17] +
          ((uint64_t)a[15]) * b[16] + ((uint64_t)a[16]) * b[15] +
          ((uint64_t)a[17]) * b[14] + ((uint64_t)a[18]) * b[13];

  r[32] = 0 + ((uint64_t)a[14]) * b[18] + ((uint64_t)a[15]) * b[17] +
          ((uint64_t)a[16]) * b[16] + ((uint64_t)a[17]) * b[15] +
          ((uint64_t)a[18]) * b[14];

  r[33] = 0 + ((uint64_t)a[15]) * b[18] + ((uint64_t)a[16]) * b[17] +
          ((uint64_t)a[17]) * b[16] + ((uint64_t)a[18]) * b[15];

  r[34] = 0 + ((uint64_t)a[16]) * b[18] + ((uint64_t)a[17]) * b[17] +
          ((uint64_t)a[18]) * b[16];

  r[35] = 0 + ((uint64_t)a[17]) * b[18] + ((uint64_t)a[18]) * b[17];

  r[36] = 0 + ((uint64_t)a[18]) * b[18];

  r[37] = 0;
}

static void sqr_nored(uint64_t r[38], const felem a) {
  r[0] = 0 
+((uint64_t)a[0])*a[0]
;

r[1] = 0 
+((uint64_t)( a[0]<<1))*a[1]
;

r[2] = 0 
+((uint64_t)( a[0]<<1))*a[2]
+((uint64_t)a[1])*a[1]
;

r[3] = 0 
+((uint64_t)( a[0]<<1))*a[3]
+((uint64_t)( a[1]<<1))*a[2]
;

r[4] = 0 
+((uint64_t)( a[0]<<1))*a[4]
+((uint64_t)( a[1]<<1))*a[3]
+((uint64_t)a[2])*a[2]
;

r[5] = 0 
+((uint64_t)( a[0]<<1))*a[5]
+((uint64_t)( a[1]<<1))*a[4]
+((uint64_t)( a[2]<<1))*a[3]
;

r[6] = 0 
+((uint64_t)( a[0]<<1))*a[6]
+((uint64_t)( a[1]<<1))*a[5]
+((uint64_t)( a[2]<<1))*a[4]
+((uint64_t)a[3])*a[3]
;

r[7] = 0 
+((uint64_t)( a[0]<<1))*a[7]
+((uint64_t)( a[1]<<1))*a[6]
+((uint64_t)( a[2]<<1))*a[5]
+((uint64_t)( a[3]<<1))*a[4]
;

r[8] = 0 
+((uint64_t)( a[0]<<1))*a[8]
+((uint64_t)( a[1]<<1))*a[7]
+((uint64_t)( a[2]<<1))*a[6]
+((uint64_t)( a[3]<<1))*a[5]
+((uint64_t)a[4])*a[4]
;

r[9] = 0 
+((uint64_t)( a[0]<<1))*a[9]
+((uint64_t)( a[1]<<1))*a[8]
+((uint64_t)( a[2]<<1))*a[7]
+((uint64_t)( a[3]<<1))*a[6]
+((uint64_t)( a[4]<<1))*a[5]
;

r[10] = 0 
+((uint64_t)( a[0]<<1))*a[10]
+((uint64_t)( a[1]<<1))*a[9]
+((uint64_t)( a[2]<<1))*a[8]
+((uint64_t)( a[3]<<1))*a[7]
+((uint64_t)( a[4]<<1))*a[6]
+((uint64_t)a[5])*a[5]
;

r[11] = 0 
+((uint64_t)( a[0]<<1))*a[11]
+((uint64_t)( a[1]<<1))*a[10]
+((uint64_t)( a[2]<<1))*a[9]
+((uint64_t)( a[3]<<1))*a[8]
+((uint64_t)( a[4]<<1))*a[7]
+((uint64_t)( a[5]<<1))*a[6]
;

r[12] = 0 
+((uint64_t)( a[0]<<1))*a[12]
+((uint64_t)( a[1]<<1))*a[11]
+((uint64_t)( a[2]<<1))*a[10]
+((uint64_t)( a[3]<<1))*a[9]
+((uint64_t)( a[4]<<1))*a[8]
+((uint64_t)( a[5]<<1))*a[7]
+((uint64_t)a[6])*a[6]
;

r[13] = 0 
+((uint64_t)( a[0]<<1))*a[13]
+((uint64_t)( a[1]<<1))*a[12]
+((uint64_t)( a[2]<<1))*a[11]
+((uint64_t)( a[3]<<1))*a[10]
+((uint64_t)( a[4]<<1))*a[9]
+((uint64_t)( a[5]<<1))*a[8]
+((uint64_t)( a[6]<<1))*a[7]
;

r[14] = 0 
+((uint64_t)( a[0]<<1))*a[14]
+((uint64_t)( a[1]<<1))*a[13]
+((uint64_t)( a[2]<<1))*a[12]
+((uint64_t)( a[3]<<1))*a[11]
+((uint64_t)( a[4]<<1))*a[10]
+((uint64_t)( a[5]<<1))*a[9]
+((uint64_t)( a[6]<<1))*a[8]
+((uint64_t)a[7])*a[7]
;

r[15] = 0 
+((uint64_t)( a[0]<<1))*a[15]
+((uint64_t)( a[1]<<1))*a[14]
+((uint64_t)( a[2]<<1))*a[13]
+((uint64_t)( a[3]<<1))*a[12]
+((uint64_t)( a[4]<<1))*a[11]
+((uint64_t)( a[5]<<1))*a[10]
+((uint64_t)( a[6]<<1))*a[9]
+((uint64_t)( a[7]<<1))*a[8]
;

r[16] = 0 
+((uint64_t)( a[0]<<1))*a[16]
+((uint64_t)( a[1]<<1))*a[15]
+((uint64_t)( a[2]<<1))*a[14]
+((uint64_t)( a[3]<<1))*a[13]
+((uint64_t)( a[4]<<1))*a[12]
+((uint64_t)( a[5]<<1))*a[11]
+((uint64_t)( a[6]<<1))*a[10]
+((uint64_t)( a[7]<<1))*a[9]
+((uint64_t)a[8])*a[8]
;

r[17] = 0 
+((uint64_t)( a[0]<<1))*a[17]
+((uint64_t)( a[1]<<1))*a[16]
+((uint64_t)( a[2]<<1))*a[15]
+((uint64_t)( a[3]<<1))*a[14]
+((uint64_t)( a[4]<<1))*a[13]
+((uint64_t)( a[5]<<1))*a[12]
+((uint64_t)( a[6]<<1))*a[11]
+((uint64_t)( a[7]<<1))*a[10]
+((uint64_t)( a[8]<<1))*a[9]
;

r[18] = 0 
+((uint64_t)( a[0]<<1))*a[18]
+((uint64_t)( a[1]<<1))*a[17]
+((uint64_t)( a[2]<<1))*a[16]
+((uint64_t)( a[3]<<1))*a[15]
+((uint64_t)( a[4]<<1))*a[14]
+((uint64_t)( a[5]<<1))*a[13]
+((uint64_t)( a[6]<<1))*a[12]
+((uint64_t)( a[7]<<1))*a[11]
+((uint64_t)( a[8]<<1))*a[10]
+((uint64_t)a[9])*a[9]
;

r[19] = 0 
+((uint64_t)( a[1]<<1))*a[18]
+((uint64_t)( a[2]<<1))*a[17]
+((uint64_t)( a[3]<<1))*a[16]
+((uint64_t)( a[4]<<1))*a[15]
+((uint64_t)( a[5]<<1))*a[14]
+((uint64_t)( a[6]<<1))*a[13]
+((uint64_t)( a[7]<<1))*a[12]
+((uint64_t)( a[8]<<1))*a[11]
+((uint64_t)( a[9]<<1))*a[10]
;

r[20] = 0 
+((uint64_t)( a[2]<<1))*a[18]
+((uint64_t)( a[3]<<1))*a[17]
+((uint64_t)( a[4]<<1))*a[16]
+((uint64_t)( a[5]<<1))*a[15]
+((uint64_t)( a[6]<<1))*a[14]
+((uint64_t)( a[7]<<1))*a[13]
+((uint64_t)( a[8]<<1))*a[12]
+((uint64_t)( a[9]<<1))*a[11]
+((uint64_t)a[10])*a[10]
;

r[21] = 0 
+((uint64_t)( a[3]<<1))*a[18]
+((uint64_t)( a[4]<<1))*a[17]
+((uint64_t)( a[5]<<1))*a[16]
+((uint64_t)( a[6]<<1))*a[15]
+((uint64_t)( a[7]<<1))*a[14]
+((uint64_t)( a[8]<<1))*a[13]
+((uint64_t)( a[9]<<1))*a[12]
+((uint64_t)( a[10]<<1))*a[11]
;

r[22] = 0 
+((uint64_t)( a[4]<<1))*a[18]
+((uint64_t)( a[5]<<1))*a[17]
+((uint64_t)( a[6]<<1))*a[16]
+((uint64_t)( a[7]<<1))*a[15]
+((uint64_t)( a[8]<<1))*a[14]
+((uint64_t)( a[9]<<1))*a[13]
+((uint64_t)( a[10]<<1))*a[12]
+((uint64_t)a[11])*a[11]
;

r[23] = 0 
+((uint64_t)( a[5]<<1))*a[18]
+((uint64_t)( a[6]<<1))*a[17]
+((uint64_t)( a[7]<<1))*a[16]
+((uint64_t)( a[8]<<1))*a[15]
+((uint64_t)( a[9]<<1))*a[14]
+((uint64_t)( a[10]<<1))*a[13]
+((uint64_t)( a[11]<<1))*a[12]
;

r[24] = 0 
+((uint64_t)( a[6]<<1))*a[18]
+((uint64_t)( a[7]<<1))*a[17]
+((uint64_t)( a[8]<<1))*a[16]
+((uint64_t)( a[9]<<1))*a[15]
+((uint64_t)( a[10]<<1))*a[14]
+((uint64_t)( a[11]<<1))*a[13]
+((uint64_t)a[12])*a[12]
;

r[25] = 0 
+((uint64_t)( a[7]<<1))*a[18]
+((uint64_t)( a[8]<<1))*a[17]
+((uint64_t)( a[9]<<1))*a[16]
+((uint64_t)( a[10]<<1))*a[15]
+((uint64_t)( a[11]<<1))*a[14]
+((uint64_t)( a[12]<<1))*a[13]
;

r[26] = 0 
+((uint64_t)( a[8]<<1))*a[18]
+((uint64_t)( a[9]<<1))*a[17]
+((uint64_t)( a[10]<<1))*a[16]
+((uint64_t)( a[11]<<1))*a[15]
+((uint64_t)( a[12]<<1))*a[14]
+((uint64_t)a[13])*a[13]
;

r[27] = 0 
+((uint64_t)( a[9]<<1))*a[18]
+((uint64_t)( a[10]<<1))*a[17]
+((uint64_t)( a[11]<<1))*a[16]
+((uint64_t)( a[12]<<1))*a[15]
+((uint64_t)( a[13]<<1))*a[14]
;

r[28] = 0 
+((uint64_t)( a[10]<<1))*a[18]
+((uint64_t)( a[11]<<1))*a[17]
+((uint64_t)( a[12]<<1))*a[16]
+((uint64_t)( a[13]<<1))*a[15]
+((uint64_t)a[14])*a[14]
;

r[29] = 0 
+((uint64_t)( a[11]<<1))*a[18]
+((uint64_t)( a[12]<<1))*a[17]
+((uint64_t)( a[13]<<1))*a[16]
+((uint64_t)( a[14]<<1))*a[15]
;

r[30] = 0 
+((uint64_t)( a[12]<<1))*a[18]
+((uint64_t)( a[13]<<1))*a[17]
+((uint64_t)( a[14]<<1))*a[16]
+((uint64_t)a[15])*a[15]
;

r[31] = 0 
+((uint64_t)( a[13]<<1))*a[18]
+((uint64_t)( a[14]<<1))*a[17]
+((uint64_t)( a[15]<<1))*a[16]
;

r[32] = 0 
+((uint64_t)( a[14]<<1))*a[18]
+((uint64_t)( a[15]<<1))*a[17]
+((uint64_t)a[16])*a[16]
;

r[33] = 0 
+((uint64_t)( a[15]<<1))*a[18]
+((uint64_t)( a[16]<<1))*a[17]
;

r[34] = 0 
+((uint64_t)( a[16]<<1))*a[18]
+((uint64_t)a[17])*a[17]
;

r[35] = 0 
+((uint64_t)( a[17]<<1))*a[18]
;

r[36] = 0 
+((uint64_t)a[18])*a[18]
;

r[37] = 0 
;
}

static void carry_prop_prod(uint64_t prod[38], int len) {
  uint64_t carry = 0;
  for (int i = 0; i < len; i++) {
    carry += prod[i];
    prod[i] = carry & bottom28;
    carry = carry >> 28;
  }
  prod[len] = carry;
}

static void multred(felem r, uint64_t prod[38]) {
  // r will be less then p, and have r[i]<2^28
  carry_prop_prod(prod, 37);
  // All prod[i] are now < 2^28, except prod[37] which is at most 2^(63-28) =
  // 2^(35). prod[37] should fit at 2^515, which is 2^11*2^(18*28). So prod[18]
  // has a 2^46 element added to it,
  // and all others are <2^39
  for (int i = 0; i < 19; i++) {
    prod[i] += prod[19 + i] << 11;
  }
  carry_prop_prod(prod, 19); // prod[19] is now<2^18
  prod[0] += prod[19] << 11;
  for (int i = 0; i < 19; i++) {
    r[i] = prod[i];
  }
  reduce_carry(r);
}

static void mult(felem r, const felem a, const felem b) {
  uint64_t prod[38];
  mult_nored(prod, a, b);
  multred(r, prod);
}

static void mul2(felem r, const felem a) { add(r, a, a); }

static void mul3(felem r, const felem a) {
  for (int i = 0; i < 19; i++) {
    r[i] = 3 * a[i];
  }
  mostly_reduce(r);
}

static void mul4(felem r, const felem a) {
  for (int i = 0; i < 19; i++) {
    r[i] = 4 * a[i];
  }
  mostly_reduce(r);
}

static void mul8(felem r, const felem a) {
  for (int i = 0; i < 19; i++) {
    r[i] = 8 * a[i];
  }
  mostly_reduce(r);
}

static void sqr(felem r, const felem a) {
  uint64_t prod[38];
  sqr_nored(prod, a);
  multred(r, prod);
}

static void mov(felem dst, const felem src) {
  for (int i = 0; i < 19; i++) {
    dst[i] = src[i];
  }
}

static void cmov(felem r, const felem a, int cond) {
  uint32_t mask = -cond;
  for (int i = 0; i < 19; i++) {
    r[i] ^= (r[i] ^ a[i]) & mask;
  }
}
static void cor(felem r, const felem a, uint32_t mask) {
  for (int i = 0; i < 19; i++) {
    r[i] |= a[i] & mask;
  }
}

static void neg_cond(felem r, const felem a, int cond) {
  // pre and post conditions same for sub
  felem tmp;
  felem zero = {0};
  sub(tmp, zero, a);
  cmov(r, a, 1 - cond);
  cmov(r, tmp, cond);
}

static bool iszero(const felem a) {
  felem t;
  mov(t, a);
  reduce_total(t);
  uint32_t d = 0;
  for (int i = 0; i < 19; i++) {
    d |= t[i];
  }
  return d == 0;
}

static bool equal(const felem a, const felem b) {
  felem t_a;
  felem t_b;
  uint32_t flag = 0;
  mov(t_a, a);
  mov(t_b, b);
  reduce_total(t_a);
  reduce_total(t_b);
  for (int i = 0; i < 19; i++) {
    flag |= a[i] ^ b[i];
  }
  return flag == 0;
}

static void unpack(felem a, const unsigned char s[66]) {
  unsigned char t[66];
  for (int i = 0; i < 66; i++) {
    t[i] = s[65 - i];
  }
  for (int i = 0; i < 9; i++) {
    a[2 * i] = (uint32_t)t[7 * i] | (t[7 * i + 1] << 8) | (t[7 * i + 2] << 16) |
               ((t[7 * i + 3] & 0xf) << 24);
    a[2 * i + 1] = (uint32_t)t[7 * i + 3] | (t[7 * i + 4] << 8) |
                   (t[7 * i + 5] << 16) | (t[7 * i + 6] << 24);
    a[2 * i + 1] >>= 4;
  }
  a[18] = t[63] | (t[64] << 8) | (t[65] << 16);
}

static void pack(unsigned char s[66], const felem a) {
  unsigned char t[66];
  felem tmp;
  assert(is_fully_reduced(a));
  for (int i = 0; i < 9; i++) {
    t[7 * i] = a[2 * i];
    t[7 * i + 1] = a[2 * i] >> 8;
    t[7 * i + 2] = a[2 * i] >> 16;
    t[7 * i + 3] = a[2 * i] >> 24;
    t[7 * i + 3] |= (a[2 * i + 1] & 0xf) << 4;
    t[7 * i + 4] = a[2 * i + 1] >> 4;
    t[7 * i + 5] = a[2 * i + 1] >> 12;
    t[7 * i + 6] = a[2 * i + 1] >> 20;
  }
  t[63] = a[18];
  t[64] = a[18] >> 8;
  t[65] = a[18] >> 16;
  for (int i = 0; i < 66; i++) {
    s[i] = t[65 - i];
  }
  unpack(tmp, s);
  if (!equal(tmp, a)) {
    for (int i = 0; i < 19; i++) {
      printf("%d, %08x, %08x\n", i, tmp[i], a[i]);
    }
  }
  assert(is_fully_reduced(a));
  assert(equal(tmp, a));
}

static void inv(felem r, const felem a) {
  felem a2, a3, a6, a7, a8, a16, a32, a64, a128, a256, a512, a519, t;
  sqr(t, a);
  mult(a2, t, a);
  mov(t, a2);
  sqr(t, t);
  mult(a3, t, a);
  mov(t, a3);
  for (int i = 0; i < 3; i++) {
    sqr(t, t);
  }
  mult(a6, t, a3);
  sqr(t, a6);
  mult(a7, t, a);
  sqr(t, a7);
  mult(a8, t, a);
  mov(t, a8);
  for (int i = 0; i < 8; i++) {
    sqr(t, t);
  }
  mult(a16, t, a8);
  mov(t, a16);
  for (int i = 0; i < 16; i++) {
    sqr(t, t);
  }
  mult(a32, t, a16);
  mov(t, a32);
  for (int i = 0; i < 32; i++) {
    sqr(t, t);
  }
  mult(a64, t, a32);
  mov(t, a64);
  for (int i = 0; i < 64; i++) {
    sqr(t, t);
  }
  mult(a128, t, a64);
  mov(t, a128);
  for (int i = 0; i < 128; i++) {
    sqr(t, t);
  }
  mult(a256, t, a128);
  mov(t, a256);
  for (int i = 0; i < 256; i++) {
    sqr(t, t);
  }
  mult(a512, t, a256);
  mov(t, a512);
  for (int i = 0; i < 7; i++) {
    sqr(t, t);
  }
  mult(a519, t, a7);
  mov(t, a519);
  for (int i = 0; i < 2; i++) {
    sqr(t, t);
  }
  mult(r, t, a);
}

static void double_pt(felem x3, felem y3, felem z3, const felem x1,
                      const felem y1, const felem z1) {
  /* As the order is not divisible by 2, impossible to double finite point and
   * get infinity */
  /* Also works for point at infinity (assuming correct representation */
  /* TODO: color to reduce stack usage*/
  /* From the EFD dbl-2001-b */
  felem delta;
  felem gamma;
  felem beta;
  felem alpha;
  felem t0;
  felem t1;
  felem t2;
  felem t3;
  felem t4;
  felem t5;
  felem t6;
  felem t7;
  felem t8;
  felem t9;
  felem t10;
  felem t11;
  felem t12;
  sqr(delta, z1);        /* delta = Z1^2 */
  sqr(gamma, y1);        /* gamma = Y1^2 */
  mult(beta, x1, gamma); /* beta = X1*gamma */
  sub(t0, x1, delta);    /* t0=X1*delta */
  add(t1, x1, delta);    /* t1 = X1+delta */
  mult(t2, t0, t1);      /* t2 = t0+t1 */
  mul3(alpha, t2);       /* alpha = 3*t2 */
  sqr(t3, alpha);        /* t3 = alpha^2 */
  mul8(t4, beta);        /* t4 = 8*beta */
  sub(x3, t3, t4);       /* X3 = t3-t4 */
  add(t5, y1, z1);       /* t5 = Y1+Z1 */
  sqr(t6, t5);           /* t6 = t5^2 */
  sub(t7, t6, gamma);    /* t7 = t6-gamma */
  sub(z3, t7, delta);    /* Z3 = t7-delta */
  mul4(t8, beta);        /* t8 = 4*beta */
  sub(t9, t8, x3);       /* t9 = t8-X3 */
  sqr(t10, gamma);       /* t10 = gamma^2 */
  mul8(t11, t10);        /* t11 = 8*t10 */
  mult(t12, alpha, t9);  /* t12 = alpha*t9 */
  sub(y3, t12, t11);     /* Y3 = t12-t11 */
}

static void add_pt_tot(felem x3, felem y3, felem z3, const felem x1,
                       const felem y1, const felem z1, const felem x2,
                       const felem y2, const felem z2) {
  /* Special cases: z1 or z2 zero=> return the other point
     if we are doubling: use the doubling.
     if we produce infinity: set the output correctly */
  /* Uses add-2007-bl. Note that test z1, z2, for pt at infinity (so return
   * other one) and H for either double or inverse (return infinity)*/
  felem z1z1;
  felem z2z2;
  felem u1;
  felem u2;
  felem t0;
  felem t1;
  felem t2;
  felem s1;
  felem s2;
  felem h;
  felem i;
  felem j;
  felem t3;
  felem r;
  felem v;
  felem t4;
  felem t5;
  felem t6;
  felem t7;
  felem t8;
  felem t9;
  felem t10;
  felem t11;
  felem t12;
  felem t13;
  felem t14;
  if (iszero(z1)) {
    mov(x3, x2);
    mov(y3, y2);
    mov(z3, z2);
    return;
  } else if (iszero(z2)) {
    mov(x3, x1);
    mov(y3, y1);
    mov(z3, z1);
    return;
  }
  mult(z1z1, z1, z1);
  mult(z2z2, z2, z2);
  mult(u1, z2z2, x1);
  mult(u2, z1z1, x2);
  mult(t0, z2, z2z2);
  mult(s1, y1, t0);
  mult(t1, z1, z1z1);
  mult(s2, y2, t1);
  sub(h, u2, u1);
  if (iszero(h)) {
    if (equal(s1, s2)) {
      double_pt(x3, y3, z3, x1, y1, z1);
      return;
    } else {
      for (int i = 0; i < 19; i++) {
        x3[i] = 0;
        y3[i] = 0;
        z3[i] = 0;
      }
      x3[0] = 1;
      y3[0] = 1;
      return;
    }
  }
  mul2(t2, h);
  mult(i, t2, t2);
  mult(j, h, i);
  sub(t3, s2, s1);
  mul2(r, t3);
  mult(v, u1, i);
  mult(t4, r, r);
  mul2(t5, v);
  sub(t6, t4, j);
  sub(x3, t6, t5);
  sub(t7, v, x3);
  mult(t8, s1, j);
  mul2(t9, t8);
  mult(t10, r, t7);
  sub(y3, t10, t9);
  add(t11, z1, z2);
  mult(t12, t11, t11);
  sub(t13, t12, z1z1);
  sub(t14, t13, z2z2);
  mult(z3, t14, h);
}

static void add_pt_const(felem x3, felem y3, felem z3, const felem x1,
                         const felem y1, const felem z1, const felem x2,
                         const felem y2, const felem z2) {
  /* Produces junk if used to add a point to itself or points at infinity. This
   * is ok: we use flags and constant time moves */
  /* Formula is from the Explicit Formula Database: add-2007-bl*/
  felem z1z1;
  felem z2z2;
  felem u1;
  felem u2;
  felem t0;
  felem t1;
  felem t2;
  felem s1;
  felem s2;
  felem h;
  felem i;
  felem j;
  felem t3;
  felem r;
  felem v;
  felem t4;
  felem t5;
  felem t6;
  felem t7;
  felem t8;
  felem t9;
  felem t10;
  felem t11;
  felem t12;
  felem t13;
  felem t14;
  sqr(z1z1, z1);       /* Z1Z1 = Z1^2 */
  sqr(z2z2, z2);       /* Z2Z2 = Z2^2 */
  mult(u1, z2z2, x1);  /* U1 = X1*Z2Z2 */
  mult(u2, z1z1, x2);  /* U2 = X2*Z1Z1 */
  mult(t0, z2, z2z2);  /* t0 = Z2*Z2Z2 */
  mult(s1, y1, t0);    /* S1 = Y1*t0 */
  mult(t1, z1, z1z1);  /* t1 = Z1*Z1Z1 */
  mult(s2, y2, t1);    /* S2 = Y2*t1 */
  sub(h, u2, u1);      /* H = U2-U1 */
  mul2(t2, h);         /* t2 = 2*H */
  sqr(i, t2);          /* I = t2^2 */
  mult(j, h, i);       /* J = H*I */
  sub(t3, s2, s1);     /* t3 = S2-S1 */
  mul2(r, t3);         /* r = 2* t3 */
  mult(v, u1, i);      /* V = U1*I */
  sqr(t4, r);          /* t4 = r^2 */
  mul2(t5, v);         /* t5 = 2*V */
  sub(t6, t4, j);      /* t6 = t4-J */
  sub(x3, t6, t5);     /* X3 = t6-t5*/
  sub(t7, v, x3);      /* t7 = V-X3 */
  mult(t8, s1, j);     /* t8 = S1*J */
  mul2(t9, t8);        /* t9 = 2*t8 */
  mult(t10, r, t7);    /* t10 = r*t7 */
  sub(y3, t10, t9);    /* Y3 = t10-t9 */
  add(t11, z1, z2);    /* t11 = Z1+Z2 */
  sqr(t12, t11);       /* t12 = t11^2 */
  sub(t13, t12, z1z1); /* t13 = t12-Z1Z1 */
  sub(t14, t13, z2z2); /* t14 = t13-Z2Z2 */
  mult(z3, t14, h);    /* Z3 = t14*H */
}

static void to_affine(felem x2, felem y2, const felem x1, const felem y1,
                      const felem z1) {
  felem zr;
  felem zrzr;
  inv(zr, z1);
  mult(zrzr, zr, zr);
  mult(x2, x1, zrzr);
  mult(zr, zrzr, zr);
  mult(y2, y1, zr);
  reduce_total(x2);
  reduce_total(y2);
}

/* Scalar multiplication and associated functions*/
static void recode(int out_d[105], int out_s[105],
                   const unsigned char key[66]) {
  /* We use a signed representation where digits are -15, -14,... 16 */
  /* Below encodes it in constant time by subtracting 32 if the 5 bit value is
   too large.*/
  int word = 0;
  int bits = 0;
  int carry = 0;
  int sub = 0;
  int bit = 0;
  int k = 0;
  /* Note that we have an almost extra byte to handle, containing only 1 bit,
   * right after a word boundary */
  for (int i = 0; i < 65; i++) {
    for (int j = 0; j < 8; j++) {
      bit = ((key[i] >> j) & 0x1);
      word |= (bit << bits);
      bits++;
      if (bits == 5) {
        word = word + carry;
        sub = word > 16;
        word = (1 - sub) * word + sub * (32 - word);
        carry = sub;
        out_d[k] = word;
        out_s[k] = sub;
        assert(word <= 16);
        k++;
        word = 0;
        bits = 0;
      }
    }
  }
  word = key[65] + carry;
  out_d[104] = word;
  out_s[104] = 0;
}
/*Scalar is little endian*/
static void scalarmult(felem x2, felem y2, felem z2, const felem px,
                       const felem py, const unsigned char scalar[66]) {
  // Double and add for now
  int s_d[105];
  int s_s[105];
  felem xT, yT, zT;
  felem xR, yR, zR;
  felem table[17][3];
  felem one = {1};
  for (int i = 0; i < 19; i++) {
    table[0][0][i] = 0;
    table[0][1][i] = 0;
    table[0][2][i] = 0;
    x2[i] = 0;
    y2[i] = 0;
    z2[i] = 0;
    xT[i] = 0;
    yT[i] = 0;
    zT[i] = 0;
  }
  x2[0] = 1;
  y2[0] = 1;
  table[0][0][0] = 1;
  table[0][1][0] = 1;
  mov(table[1][0], px);
  mov(table[1][1], py);
  mov(table[1][2], one);
  for (int i = 2; i < 17; i++) {
    if (i % 2 == 0) {
      double_pt(table[i][0], table[i][1], table[i][2], table[i / 2][0],
                table[i / 2][1], table[i / 2][2]);
    } else {
      add_pt_const(table[i][0], table[i][1], table[i][2], table[i - 1][0],
                   table[i - 1][1], table[i - 1][2], px, py, one);
    }
  }
  recode(s_d, s_s, scalar);
  int seen = 0;
  int must_double = 0;
  int index;
  int valid_entry;
  for (int i = 104; i >= 0; i--) {
    if (must_double) {
      double_pt(x2, y2, z2, x2, y2, z2);
      double_pt(x2, y2, z2, x2, y2, z2);
      double_pt(x2, y2, z2, x2, y2, z2);
      double_pt(x2, y2, z2, x2, y2, z2);
      double_pt(x2, y2, z2, x2, y2, z2);
    }
    must_double = 1;
    index = s_d[i];
    for (int k = 0; k < 19; k++) {
      xT[k] = 0;
      yT[k] = 0;
      zT[k] = 0;
    }
    for (int k = 0; k < 17; k++) {
      uint32_t mask = -(k == index);
      cor(xT, table[k][0], mask);
      cor(yT, table[k][1], mask);
      cor(zT, table[k][2], mask);
    }
    valid_entry = (index != 0);
    neg_cond(zT, zT, s_s[i]);
    add_pt_const(xR, yR, zR, x2, y2, z2, xT, yT, zT);
    cmov(xR, xT, !seen);
    cmov(yR, yT, !seen);
    cmov(zR, zT, !seen);
    cmov(x2, xR, valid_entry);
    cmov(y2, yR, valid_entry);
    cmov(z2, zR, valid_entry);
    seen |= valid_entry;
  }
}

static void double_scalarmult(felem x3, felem y3, felem z3,
                              const unsigned char s1[66], const felem x1,
                              const felem y1, const unsigned char s2[66],
                              const felem x2, const felem y2) {
  felem one = {1};
  int s1_s[105];
  int s1_d[105];
  int s2_s[105];
  int s2_d[105];
  felem table1[17][3];
  felem table2[17][3];
  felem yT;
  int must_double = 0;
  int index;
  for (int i = 0; i < 19; i++) {
    x3[i] = 0;
    y3[i] = 0;
    z3[i] = 0;
  }
  x3[0] = 1;
  y3[0] = 1;
  for (int i = 0; i < 19; i++) {
    table1[0][0][i] = 0;
    table1[0][1][i] = 0;
    table1[0][2][i] = 0;
    table2[0][0][i] = 0;
    table2[0][1][i] = 0;
    table2[0][2][i] = 0;
  }
  mov(table1[1][0], x1);
  mov(table1[1][1], y1);
  mov(table1[1][2], one);
  mov(table2[1][0], x2);
  mov(table2[1][1], y2);
  mov(table2[1][2], one);
  for (int i = 2; i < 17; i++) {
    if (i % 2 == 0) {
      double_pt(table1[i][0], table1[i][1], table1[i][2], table1[i / 2][0],
                table1[i / 2][1], table1[i / 2][2]);
      double_pt(table2[i][0], table2[i][1], table2[i][2], table2[i / 2][0],
                table2[i / 2][1], table2[i / 2][2]);
    } else {
      add_pt_const(table1[i][0], table1[i][1], table1[i][2], table1[i - 1][0],
                   table1[i - 1][1], table1[i - 1][2], x1, y1, one);
      add_pt_const(table2[i][0], table2[i][1], table2[i][2], table2[i - 1][0],
                   table2[i - 1][1], table2[i - 1][2], x2, y2, one);
    }
  }
  recode(s1_d, s1_s, s1);
  recode(s2_d, s2_s, s2);
  for (int i = 104; i >= 0; i--) {
    if (must_double) {
      double_pt(x3, y3, z3, x3, y3, z3);
      double_pt(x3, y3, z3, x3, y3, z3);
      double_pt(x3, y3, z3, x3, y3, z3);
      double_pt(x3, y3, z3, x3, y3, z3);
      double_pt(x3, y3, z3, x3, y3, z3);
    }
    must_double = 1;
    index = s1_d[i];
    mov(yT, table1[index][1]);
    neg_cond(yT, yT, s1_s[i]);
    add_pt_tot(x3, y3, z3, x3, y3, z3, table1[index][0], yT, table1[index][2]);
    index = s2_d[i];
    mov(yT, table2[index][1]);
    neg_cond(yT, yT, s2_s[i]);
    add_pt_tot(x3, y3, z3, x3, y3, z3, table2[index][0], yT, table2[index][2]);
  }
}
/* Publically visible functions */
void p521_32_scalarmult(unsigned char q[132], const unsigned char n[66],
                        const unsigned char p[132]) {
  felem xin;
  felem yin;
  felem x2;
  felem y2;
  felem z2;
  felem xout;
  felem yout;
  unpack(xin, p);
  unpack(yin, p + 66);
  scalarmult(x2, y2, z2, xin, yin, n);
  to_affine(xout, yout, x2, y2, z2);
  pack(q, xout);
  pack(q + 66, yout);
}

void p521_32_scalarmult_base(unsigned char q[132], const unsigned char n[66]) {
  felem x2;
  felem y2;
  felem z2;
  felem xout;
  felem yout;
  scalarmult(x2, y2, z2, base_x, base_y, n);
  to_affine(xout, yout, x2, y2, z2);
  pack(q, xout);
  pack(q + 66, yout);
}

void p521_32_double_scalarmult_base(unsigned char *q,
                                    const unsigned char a[132],
                                    const unsigned char s1[66],
                                    const unsigned char s2[66]) {
  felem x2, y2;
  felem x3, y3, z3;
  felem xout, yout;
  unpack(x2, a);
  unpack(y2, a + 66);
  double_scalarmult(x3, y3, z3, s1, base_x, base_y, s2, x2, y2);
  to_affine(xout, yout, x3, y3, z3);
  pack(q, xout);
  pack(q + 66, yout);
}
