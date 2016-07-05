/* Copyright (c) Watson Ladd (Mozilla) 2016 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include <fcntl.h>
#include <stdbool.h>
#include <stdio.h>
#include <gmp.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "p384_32.h"
void randombytes(unsigned char *bytes, unsigned int len){
  int fd=-1;
  int temp;
  while(fd==-1){
    fd=open("/dev/random", O_RDONLY);
  }
  while(len){
    temp=read(fd, bytes, len);
    bytes += temp;
    len -= temp;
  }
  close(fd);
}
//All our byte arrays are supposed to be little endian.
static void
ecdsa_sign(unsigned char signature[96], const unsigned char digest[48], const unsigned char keyb[48]){
  unsigned char kbuf[96];
  unsigned char kexp[48];
  unsigned char point[96];
  for(int i=0; i<48; i++){
    kexp[i]=0;
  }
  mpz_t order;
  mpz_t k;
  mpz_t kinv;
  mpz_t x; //x coordinate
  mpz_t d; //digest
  mpz_t key; //key
  mpz_init(order);
  mpz_init(k);
  mpz_init(x);
  mpz_init(d);
  mpz_init(key);
  mpz_init(kinv);
  mpz_set_str(order, "39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643", 10);
  randombytes(kbuf, 96);
  mpz_import(k, 96, -1, 1, 1, 0, kbuf);
  mpz_mod(k, k, order);
  mpz_export(kexp, NULL, -1, 1, 1, 0, k);
  p384_32_scalarmult_base(point, kexp);
  mpz_import(x, 48, 1, 1, 1, 0, point);
  mpz_mod(x, x, order);
  mpz_import(d, 48, -1, 1, 1, 0, digest);
  mpz_import(key, 48, -1, 1, 1, 0, keyb);
  mpz_invert(kinv, k, order);
  mpz_addmul(d, x, key);
  mpz_mod(d, d, order);
  mpz_mul(d, kinv, d);
  mpz_mod(d, d, order);
  for(int i=0; i<96; i++){
    signature[i]=0;
  }
  mpz_export(signature, NULL, -1, 1, 1, 0, x);
  mpz_export(signature+48, NULL, -1, 1, 1, 0, d);
  mpz_clear(order);
  mpz_clear(k);
  mpz_clear(kinv);
  mpz_clear(x);
  mpz_clear(d);
  mpz_clear(key);
}

static int
ecdsa_verify(unsigned char signature[96], const unsigned char digest[48], const unsigned char pkey[96]){
  unsigned char u1buf[48];
  unsigned char u2buf[48];
  unsigned char point[96];
  mpz_t order;
  mpz_t s;
  mpz_t r;
  mpz_t z;
  mpz_t u1;
  mpz_t u2;
  mpz_t w;
  int ret;
  mpz_init(order);
  mpz_init(s);
  mpz_init(r);
  mpz_init(z);
  mpz_init(u1);
  mpz_init(u2);
  mpz_init(w);
  mpz_set_str(order, "39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643", 10);
  mpz_import(r, 48, -1, 1, 1, 0, signature);
  mpz_import(s, 48, -1, 1, 1, 0, signature+48);
  mpz_import(z, 48, -1, 1, 1, 0, digest);
  mpz_invert(w, s, order);
  mpz_mul(u2, r, w);
  mpz_mul(u1, z, w);
  mpz_mod(u2, u2, order);
  mpz_mod(u1, u1, order);
  for(int i=0; i<48; i++){
    u1buf[i]=0;
    u2buf[i]=0;
  }
  mpz_export(u1buf, NULL, -1, 1, 1, 0, u1);
  mpz_export(u2buf, NULL, -1, 1, 1, 0, u2);
  p384_32_double_scalarmult_base(point, pkey, u1buf, u2buf);
  mpz_import(u1, 48, 1, 1, 1, 0, point);
  mpz_sub(s, r, u1);
  mpz_mod(s, s, order);
  if(mpz_sgn(s)==0){
    ret=1;
  } else {
    ret=0;
  }
  mpz_clear(order);
  mpz_clear(s);
  mpz_clear(r);
  mpz_clear(z);
  mpz_clear(u1);
  mpz_clear(u2);
  mpz_clear(w);
  return ret;
}

int main(){
  unsigned char key[48];
  unsigned char pkey[96];
  unsigned char digest[48];
  unsigned char signature[96];
  for(int i=0; i<100; i++){
    randombytes(key, 48);
    randombytes(digest, 48);
    key[47]=0;
    p384_32_scalarmult_base(pkey, key);
    ecdsa_sign(signature, digest, key);
    if(!ecdsa_verify(signature, digest, pkey)){
      printf("Ecdsa fail\n");
    }
  }
}
