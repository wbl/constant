#include<assert.h>
#include<fcntl.h>
#include<stdint.h>
#include<stdio.h>
#include<unistd.h>
/* Copyright (c) Watson Ladd (Mozilla) 2016 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

/* A 32 bit constant time implementation of P521. Use saturated
   ordinary arithmetic with NIST reduction method. The top word is
   only 9 bits, and so we don't carry out of it on additions*/

typedef uint32_t felem[17];

static felem prime = {0xffffffff,
                      0xffffffff,
                      0xffffffff,
                      0xffffffff,
                      0xffffffff,
                      0xffffffff,
                      0xffffffff,
                      0xffffffff,
                      0xffffffff,
                      0xffffffff,
                      0xffffffff,
                      0xffffffff,
                      0xffffffff,
                      0xffffffff,
                      0xffffffff,
                      0xffffffff,
                      0x1ff};

static uint64_t mask_lo = 0x00000000ffffffff;

static void print_elem(char *name, const felem a){
  printf("%s = 0 ", name);
  for(int i=0; i<17; i++){
    printf(" + 2**(32*%d)*%u", i, a[i]);
  }
  printf("\n");
}

/* Field Arithmetic */
static void reduce_add_sub(felem a){
  uint64_t t;
  felem d;
  uint32_t b = 0;
  uint32_t pb = 0;
  uint32_t do_sub;
  uint32_t mask_sub;
  uint32_t mask_nosub;
  for (int i = 0; i < 17; i++) {
    t = (uint64_t)prime[i] + pb;
    b = a[i] < t;
    t = a[i] - t + ((uint64_t)b << 32);
    d[i] = (uint32_t)t & mask_lo;
    pb = b;
  }
  do_sub = 1 - pb;
  mask_sub = (uint32_t)-do_sub;
  mask_nosub = ~mask_sub;
  for(int i=0; i<17; i++){
    a[i] = (mask_nosub & a[i])|(mask_sub & d[i]);
  }
}

static void add(felem r, const felem a, const felem b){
  uint32_t carry = 0;
  uint64_t t;
  print_elem("a", a);
  print_elem("b", b);
  for (int i = 0; i < 17; i++) {
    t = (uint64_t)a[i] + (uint64_t)b[i] + carry;
    r[i] = (uint32_t)(t & mask_lo);
    carry = t >> 32;
  }
  assert(carry==0);
  print_elem("r_nored", r);
  reduce_add_sub(r);
  print_elem("r_red", r);
  printf("print \"add_nored\", (a+b) %% prime == r_nored %% prime \n");
  printf("print \"redcheck\", r_red %% prime == r_nored %% prime \n");
}


static void
sub(felem r, const felem a, const felem b)
{ /* Will need testing*/
  uint32_t carry = 0;
  uint64_t t = 0;
  uint32_t brw = 0;
  uint32_t pbrw = 0;
  print_elem("a", a);
  print_elem("b", b);
  for (int i = 0; i < 17; i++) { /* Assembler would be great for this.*/
    t = (uint64_t)prime[i] + a[i] + carry;
    brw = t < ((uint64_t)b[i]) + pbrw;
    t += ((uint64_t)brw) << 32;
    t -= (uint64_t)b[i] + (uint64_t)pbrw;
    r[i] = (uint32_t)(t & mask_lo);
    carry = t >> 32;
    pbrw = brw;
  }
  assert(carry==0);
  assert(pbrw == 0);
  print_elem("r_nored", r);
  printf("print \"sub_nored\", (prime+a-b) %% prime == r_nored %% prime \n");
  reduce_add_sub(r);
  print_elem("r_red", r);
  printf("print \"redcheck\", r_red %% prime == r_nored %% prime \n");
}

static void
mulred(felem r, const uint32_t t[33]){ /* This is the correct size, even if mult loop uses extra word */
  felem a;
  felem b;
  for(int i=0; i<17; i++){
    a[i]=t[i];
  }
  a[16] &= 0x1ff;
  for(int i=0; i<16; i++){
    b[i] = (t[16+i]>>9) | (t[17+i] & 0x1ff) << 23;
  }
  b[16] = t[32]>>9;
  add(r, a, b);
}

static void
mul_nored(uint32_t prod[34], felem a, felem b){
  uint64_t t;
  uint32_t carry;
  for (int i = 0; i < 34; i++) {
    prod[i] = 0;
  }
  for (int i = 0; i < 17; i++) { /*TODO: Karastuba?*/
    carry = 0;
    for (int j = 0; j < 17; j++) {
      t = ((uint64_t)a[i]) * b[j] + carry + prod[i + j];
      prod[i + j] = (uint32_t)(t & mask_lo);
      carry = t >> 32;
    }
    prod[17 + i] = carry;
  }
}

static void
mult(felem r, felem a, felem b){
  uint32_t prod[34];
  print_elem("am", a);
  print_elem("bm", b);
  mul_nored(prod, a, b);
  printf("prod_nored = 0");
  for(int i=0; i<34; i++){
    printf("+2**(32*%d)*%u", i, prod[i]);
  }
  printf("\n");
  mulred(r, prod);
  print_elem("prod", r);
  printf("print \"prod_nored\", prod_nored == am*bm\n");
  printf("print \"prod_red\", prod == prod_nored %% prime\n");
}

/* I/O */
static void
pack(unsigned char s[66], const felem b){
  s[0] = (b[16] & (0x100)) >> 8;
  s[1] = b[16] & 0xff;
  for(int i = 0; i<16; i++){
    s[(16-i)*4-2] = (b[i] >> 24) & 0xff;
    s[(16-i)*4-1] = (b[i] >> 16) & 0xff;
    s[(16-i)*4 ] = (b[i] >> 8) & 0xff;
    s[(16-i)*4 +1] = b[i] & 0xff;
  }
}

static void
unpack(felem b, unsigned char s[66]){
  for(int i=0; i<16; i++){
    b[i] = s[(16-i)*4+1] |
      s[(16-i)*4] << 8 |
      s[(16-i)*4-1] << 16 |
      s[(16-i)*4-2] << 24;
  }
  b[16] = s[0]<<8 | s[1];
}

/* Curve arithmetic */

int main(){
  print_elem("prime", prime);
  printf("print prime == 2**521-1\n");
  felem a, b, c;
  unsigned char s_a[66], s_b[66];
  int fd = open("/dev/urandom", O_RDONLY);
  for(int i=0; i<10; i++){
    read(fd, s_a, 66);
    read(fd, s_b, 66);
    s_a[0] &= 0x01;
    s_b[0] &= 0x01;
    unpack(a, s_a);
    unpack(b, s_b);
    add(c, a, b);
    sub(c, a, b);
    mult(c, a, b);
  }
}
