#include<assert.h>
#include<fcntl.h>
#include<stdbool.h>
#include<stdint.h>
#include<stdio.h>
#include<unistd.h>
#include "p521_32.h"
/* Copyright (c) Watson Ladd (Mozilla) 2016 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

/* A 32 bit constant time implementation of P521. Use saturated
   ordinary arithmetic with NIST reduction method. The top word is
   only 9 bits, and so we don't carry out of it on additions*/

/* Constants */
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

static felem curveb={0x6b503f00,
                     0xef451fd4,
                     0x3d2c34f1,
                     0x3573df88,
                     0x3bb1bf07,
                     0x1652c0bd,
                     0xec7e937b,
                     0x56193951,
                     0x8ef109e1,
                     0xb8b48991,
                     0x99b315f3,
                     0xa2da725b,
                     0xb68540ee,
                     0x929a21a0,
                     0x8e1c9a1f,
                     0x953eb961,
                     0x51};

static felem base_x = {0xc2e5bd66,
                       0xf97e7e31,
                       0x856a429b,
                       0x3348b3c1,
                       0xa2ffa8de,
                       0xfe1dc127,
                       0xefe75928,
                       0xa14b5e77,
                       0x6b4d3dba,
                       0xf828af60,
                       0x53fb521,
                       0x9c648139,
                       0x2395b442,
                       0x9e3ecb66,
                       0x404e9cd,
                       0x858e06b7,
                       0xc6};

static felem base_y ={0x9fd16650,
                      0x88be9476,
                      0xa272c240,
                      0x353c7086,
                      0x3fad0761,
                      0xc550b901,
                      0x5ef42640,
                      0x97ee7299,
                      0x273e662c,
                      0x17afbd17,
                      0x579b4468,
                      0x98f54449,
                      0x2c7d1bd9,
                      0x5c8a5fb4,
                      0x9a3bc004,
                      0x39296a78,
                      0x118};
/* Debugging */
static void print_elem(char *name, const felem a){
  printf("%s = 0 ", name);
  for(int i=0; i<17; i++){
    printf(" + 2**(32*%d)*%u", i, a[i]);
  }
  printf("\n");
}

static bool less_p(const felem b){
  int i=16;
  while(b[i]==prime[i]) i--;
  if(i<0) return false;
  return b[i]<= prime[i];
}

/* Field Arithmetic */

static void reduce_add_sub(felem a){
  uint32_t carry;
  felem d;
  uint32_t b = 0;
  uint32_t pb = 0;
  uint32_t do_sub;
  uint32_t mask_sub;
  uint32_t mask_nosub;
  //Add one
  carry = 1;
  for (int i = 0; i < 17; i++) {
    d[i] = a[i]+carry;
    carry = d[i]<a[i];
  }
  assert(carry==0);
  do_sub = (d[16] & 0x200)>>9; //if x<p, x+1<2^521
  d[16] = d[16]&0x1ff;
  mask_sub = (uint32_t)-do_sub;
  mask_nosub = ~mask_sub;
  for(int i=0; i<17; i++){
    a[i] = (mask_nosub & a[i])|(mask_sub & d[i]);
  }
}

static void neg_cond(felem r, const felem a, uint32_t cond){
  uint64_t t;
  felem d;
  uint32_t b =0;
  uint32_t pb = 0;
  uint32_t mask_cond;
  uint32_t mask_nocond;
  for(int i=0; i<17; i++){
    t = (uint64_t) prime[i];
    b = t < (uint64_t) a[i]+pb;
    t = t - a[i]+((uint64_t)b <<32);
    d[i] = (uint32_t) t & mask_lo;
    pb = b;
  }
  mask_cond = (uint32_t) -cond;
  mask_nocond = ~mask_cond;
  for(int i=0; i<17; i++){
    r[i] = (mask_cond &d[i]) | (mask_nocond & a[i]);
  }
}

static void add(felem r, const felem a, const felem b){
  uint32_t carry = 0;
  uint64_t t;
  for (int i = 0; i < 17; i++) {
    t = (uint64_t)a[i] + (uint64_t)b[i] + carry;
    r[i] = (uint32_t)(t & mask_lo);
    carry = t >> 32;
  }
  reduce_add_sub(r);
}


static void
sub(felem r, const felem a, const felem b)
{ /* Will need testing*/
  uint32_t carry = 0;
  uint64_t t = 0;
  uint32_t brw = 0;
  uint32_t pbrw = 0;
  for (int i = 0; i < 17; i++) { /* Assembler would be great for this.*/
    t = (uint64_t)prime[i] + a[i] + carry;
    brw = t < ((uint64_t)b[i]) + pbrw;
    t += ((uint64_t)brw) << 32;
    t -= (uint64_t)b[i] + (uint64_t)pbrw;
    r[i] = (uint32_t)(t & mask_lo);
    carry = t >> 32;
    pbrw = brw;
  }
  reduce_add_sub(r);
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
mul_nored(uint32_t prod[34], const felem a, const felem b){
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
sqr(felem r, const felem a){
  uint32_t prod[34];
  uint64_t t;
  uint32_t carry;
  for (int i = 0; i < 34; i++) {
    prod[i] = 0;
  }

  for (int i = 0; i < 17; i++) {
    carry = 0;
    for (int j = i + 1; j < 17; j++) {
      t = ((uint64_t)a[i]) * a[j] + carry + prod[i + j];
      prod[i + j] = (uint32_t)(t & mask_lo);
      carry = t >> 32;
    }
    prod[17 + i] = carry;
  }
  carry = 0;
  for (int i = 0; i < 34; i++) {
    t = ((uint64_t)prod[i]) * 2 + carry;
    prod[i] = (uint32_t)t;
    carry = t >> 32;
  }
  carry = 0;
  for (int i = 0; i < 17; i++) {
    t = ((uint64_t)a[i]) * a[i] + carry + prod[2 * i];
    prod[2 * i] = t & mask_lo;
    carry = t >> 32;
    t = ((uint64_t)prod[2 * i + 1]) + carry;
    prod[2 * i + 1] = t & mask_lo;
    carry = t >> 32;
  }
  mulred(r, prod);
}

static void
mult(felem r, const felem a, const felem b){
  uint32_t prod[34];
  mul_nored(prod, a, b);
  mulred(r, prod);
}

static void
mul2(felem c, const felem a)
{
  add(c, a, a);
}
static void
mul3(felem c, const felem a)
{
  mul2(c, a);
  add(c, c, a);
}

static void
mul4(felem c, const felem a)
{
  mul2(c, a);
  mul2(c, c);
}

static void
mul8(felem c, const felem a)
{
  felem t;
  mul2(c, a);
  mul2(t, c);
  mul2(c, t);
}

static void
mov(felem r, const felem a)
{
  for (int i = 0; i < 17; i++) {
    r[i] = a[i];
  }
}

static void
inv(felem r, const felem a)
{
  felem a2, a3, a6, a7, a8, a16, a32, a64, a128, a256, a512, a519, t;
  sqr(t, a);
  mult(a2, t, a);
  mov(t, a2);
  sqr(t,t);
  mult(a3, t, a);
  mov(t, a3);
  for(int i=0; i<3; i++){
    sqr(t, t);
  }
  mult(a6, t, a3);
  sqr(t, a6);
  mult(a7, t, a);
  sqr(t, a7);
  mult(a8, t, a);
  mov(t, a8);
  for(int i=0; i<8; i++){
    sqr(t, t);
  }
  mult(a16, t, a8);
  mov(t, a16);
  for(int i=0; i<16; i++){
    sqr(t, t);
  }
  mult(a32, t, a16);
  mov(t, a32);
  for(int i=0; i<32; i++){
    sqr(t, t);
  }
  mult(a64, t, a32);
  mov(t, a64);
  for(int i=0; i<64; i++){
    sqr(t, t);
  }
  mult(a128, t, a64);
  mov(t, a128);
  for(int i=0; i<128; i++){
    sqr(t, t);
  }
  mult(a256, t, a128);
  mov(t, a256);
  for(int i=0; i<256; i++){
    sqr(t, t);
  }
  mult(a512, t, a256);
  mov(t, a512);
  for(int i=0; i<7; i++){
    sqr(t, t);
  }
  mult(a519, t, a7);
  mov(t, a519);
  for(int i=0; i<2; i++){
    sqr(t, t);
  }
  mult(r, t, a);
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
unpack(felem b, const unsigned char s[66]){
  for(int i=0; i<16; i++){
    b[i] = s[(16-i)*4+1] |
      s[(16-i)*4] << 8 |
      s[(16-i)*4-1] << 16 |
      s[(16-i)*4-2] << 24;
  }
  b[16] = s[0]<<8 | s[1];
}

static bool
equal(const felem a, const felem b)
{ // Can leak *result*
  uint32_t diff = 0;
  for (int i = 0; i < 17; i++) {
    diff |= a[i] ^ b[i];
  }
  return diff == 0;
}

static bool
iszero(const felem a)
{
  uint32_t test = 0;
  for (int i = 0; i < 17; i++) {
    test |= a[i];
  }
  return test == 0;
}

static void
cmov(felem r, const felem a, uint32_t cond)
{
  uint32_t mask_set;
  uint32_t mask_unset;
  mask_set = (uint32_t)-cond;
  mask_unset = ~mask_set;
  for (int i = 0; i < 17; i++) {
    r[i] = (r[i] & mask_unset) | (a[i] & mask_set);
  }
}

/* Curve arithmetic */

static void
double_pt(felem x3, felem y3, felem z3, const felem x1, const felem y1,
          const felem z1)
{
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
  sqr(delta, z1); /* delta = Z1^2 */
  sqr(gamma, y1); /* gamma = Y1^2 */
  mult(beta, x1, gamma); /* beta = X1*gamma */
  sub(t0, x1, delta); /* t0=X1*delta */
  add(t1, x1, delta); /* t1 = X1+delta */
  mult(t2, t0, t1);  /* t2 = t0+t1 */
  mul3(alpha, t2); /* alpha = 3*t2 */
  sqr(t3, alpha); /* t3 = alpha^2 */
  mul8(t4, beta); /* t4 = 8*beta */
  sub(x3, t3, t4); /* X3 = t3-t4 */
  add(t5, y1, z1); /* t5 = Y1+Z1 */
  sqr(t6, t5); /* t6 = t5^2 */
  sub(t7, t6, gamma); /* t7 = t6-gamma */
  sub(z3, t7, delta); /* Z3 = t7-delta */
  mul4(t8, beta); /* t8 = 4*beta */
  sub(t9, t8, x3); /* t9 = t8-X3 */
  sqr(t10, gamma); /* t10 = gamma^2 */
  mul8(t11, t10); /* t11 = 8*t10 */
  mult(t12, alpha, t9); /* t12 = alpha*t9 */
  sub(y3, t12, t11); /* Y3 = t12-t11 */
}

static void
add_pt_tot(felem x3, felem y3, felem z3, const felem x1, const felem y1,
           const felem z1, const felem x2, const felem y2, const felem z2)
{
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
      for(int i=0; i<17; i++){
        x3[i]=0;
        y3[i]=0;
	z3[i]=0;
      }
      x3[0]=1;
      y3[0]=1;
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

static void
readd_pt_tot(felem x3, felem y3, felem z3, const felem x1, const felem y1,
	     const felem z1, const felem x2, const felem y2, const felem z2,
	     const felem z2z2, const felem z2z2z2)
{
  /* Special cases: z1 or z2 zero=> return the other point
     if we are doubling: use the doubling.
     if we produce infinity: set the output correctly */
  /* Uses add-2007-bl. Note that test z1, z2, for pt at infinity (so return
   * other one) and H for either double or inverse (return infinity)*/
  felem z1z1;
  felem u1;
  felem u2;
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
  mult(u1, z2z2, x1);
  mult(u2, z1z1, x2);
  mult(s1, y1, z2z2z2);
  mult(t1, z1, z1z1);
  mult(s2, y2, t1);
  sub(h, u2, u1);
  if (iszero(h)) {
    if (equal(s1, s2)) {
      double_pt(x3, y3, z3, x1, y1, z1);
      return;
    } else {
      for(int i=0; i<17; i++){
        x3[i]=0;
        y3[i]=0;
	z3[i]=0;
      }
      x3[0]=1;
      y3[0]=1;
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

static void
add_pt_const(felem x3, felem y3, felem z3, const felem x1, const felem y1,
             const felem z1, const felem x2, const felem y2, const felem z2)
{
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
  sqr(z1z1, z1); /* Z1Z1 = Z1^2 */
  sqr(z2z2, z2); /* Z2Z2 = Z2^2 */
  mult(u1, z2z2, x1); /* U1 = X1*Z2Z2 */
  mult(u2, z1z1, x2); /* U2 = X2*Z1Z1 */
  mult(t0, z2, z2z2); /* t0 = Z2*Z2Z2 */
  mult(s1, y1, t0); /* S1 = Y1*t0 */
  mult(t1, z1, z1z1); /* t1 = Z1*Z1Z1 */
  mult(s2, y2, t1); /* S2 = Y2*t1 */
  sub(h, u2, u1); /* H = U2-U1 */
  mul2(t2, h); /* t2 = 2*H */
  sqr(i, t2); /* I = t2^2 */
  mult(j, h, i); /* J = H*I */
  sub(t3, s2, s1); /* t3 = S2-S1 */
  mul2(r, t3); /* r = 2* t3 */
  mult(v, u1, i); /* V = U1*I */
  sqr(t4, r); /* t4 = r^2 */
  mul2(t5, v); /* t5 = 2*V */
  sub(t6, t4, j); /* t6 = t4-J */
  sub(x3, t6, t5); /* X3 = t6-t5*/
  sub(t7, v, x3); /* t7 = V-X3 */
  mult(t8, s1, j); /* t8 = S1*J */
  mul2(t9, t8); /* t9 = 2*t8 */
  mult(t10, r, t7); /* t10 = r*t7 */
  sub(y3, t10, t9); /* Y3 = t10-t9 */
  add(t11, z1, z2); /* t11 = Z1+Z2 */
  sqr(t12, t11); /* t12 = t11^2 */
  sub(t13, t12, z1z1); /* t13 = t12-Z1Z1 */
  sub(t14, t13, z2z2); /* t14 = t13-Z2Z2 */
  mult(z3, t14, h); /* Z3 = t14*H */
}

static void
readd_pt_const(felem x3, felem y3, felem z3, const felem x1, const felem y1,
               const felem z1, const felem x2, const felem y2, const felem z2,
               const felem z2z2, const felem z2z2z2)
{
  /* Produces junk if used to add a point to itself or points at infinity. This
   * is ok: we use flags and constant time moves*/
  /* Same as above code, only removes some calculations that are passed in*/
  felem z1z1;
  felem u1;
  felem u2;
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
  sqr(z1z1, z1);
  mult(u1, z2z2, x1);
  mult(u2, z1z1, x2);
  mult(s1, y1, z2z2z2);
  mult(t1, z1, z1z1);
  mult(s2, y2, t1);
  sub(h, u2, u1);
  mul2(t2, h);
  sqr(i, t2);
  mult(j, h, i);
  sub(t3, s2, s1);
  mul2(r, t3);
  mult(v, u1, i);
  sqr(t4, r);
  mul2(t5, v);
  sub(t6, t4, j);
  sub(x3, t6, t5);
  sub(t7, v, x3);
  mult(t8, s1, j);
  mul2(t9, t8);
  mult(t10, r, t7);
  sub(y3, t10, t9);
  add(t11, z1, z2);
  sqr(t12, t11);
  sub(t13, t12, z1z1);
  sub(t14, t13, z2z2);
  mult(z3, t14, h);
}

static void
to_affine(felem x2, felem y2, const felem x1, const felem y1, const felem z1)
{
  felem zr;
  felem zrzr;
  inv(zr, z1);
  mult(zrzr, zr, zr);
  mult(x2, x1, zrzr);
  mult(zr, zrzr, zr);
  mult(y2, y1, zr);
}

static bool
oncurve(const felem x, const felem y, const felem z)
{
  felem z2, z4, z6, t0, t1, t2, t3, t4, t5, ysqr, rhs;
  mult(z2, z, z);
  mult(z4, z2, z2);
  mult(z6, z4, z2);
  mult(t0, curveb, z6);
  mult(t1, x, z4);
  mul3(t2, t1);
  mult(t3, x, x);
  mult(t4, t3, x);
  sub(t5, t4, t2);
  add(rhs, t5, t0);
  mult(ysqr, y, y);
  return equal(ysqr, rhs);
}
/* Scalar multiplication and associated functions*/
static void
recode(int out_d[105], int out_s[105], const unsigned char key[66])
{
  /* We use a signed representation where digits are -15, -14,... 16 */
  /* Below encodes it in constant time by subtracting 32 if the 5 bit value is
   too large.*/
  int word = 0;
  int bits = 0;
  int carry = 0;
  int sub = 0;
  int bit = 0;
  int k = 0;
  /* Note that we have an almost extra byte to handle, containing only 1 bit, right after a word boundary */
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
	assert(word<=16);
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
static void
scalarmult(felem x2, felem y2, felem z2, const felem px, const felem py, const unsigned char scalar[66]){
  //Double and add for now
  int s_d[105];
  int s_s[105];
  felem xT, yT, zT;
  felem xR, yR, zR;
  felem table[17][3];
  felem one={1};
  for(int i=0; i<17; i++){
    table[0][0][i]=0;
    table[0][1][i]=0;
    table[0][2][i]=0;
    x2[i]=0;
    y2[i]=0;
    z2[i]=0;
  }
  x2[0]=1;
  y2[0]=1;
  table[0][0][0]=1;
  table[0][1][0]=1;
  mov(table[1][0], px);
  mov(table[1][1], py);
  mov(table[1][2], one);
  for(int i=2; i<17; i++){
    if(i%2==0){
      double_pt(table[i][0], table[i][1], table[i][2], table[i/2][0], table[i/2][1], table[i/2][2]);
    }else {
      add_pt_const(table[i][0], table[i][1], table[i][2], table[i-1][0], table[i-1][1], table[i-1][2],
             px, py, one);
    }
  }
  recode(s_d, s_s, scalar);
  int seen = 0;
  int must_double = 0;
  int index;
  int valid_entry;
  for(int i=104; i>=0; i--){
    if(must_double){
      double_pt(x2, y2, z2, x2, y2, z2); 
      double_pt(x2, y2, z2, x2, y2, z2); 
      double_pt(x2, y2, z2, x2, y2, z2);
      double_pt(x2, y2, z2, x2, y2, z2);
      double_pt(x2, y2, z2, x2, y2, z2);
    }
    must_double = 1;
    index = s_d[i];
    for(int k=0; k<17; k++){
      cmov(xT, table[k][0], k==index);
      cmov(yT, table[k][1], k==index);
      cmov(zT, table[k][2], k==index);
      }
    valid_entry = (index!=0);
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

static void
double_scalarmult(felem x3, felem y3, felem z3, const unsigned char s1[66], const felem x1, const felem y1, const unsigned char s2[66], const felem x2, const felem y2){
  for(int i=0; i<17; i++){
    x3[i]=0;
    y3[i]=0;
    z3[i]=0;
  }
  x3[0]=1;
  y3[0]=1;
  felem one={1};
  for(int i=65; i>=0; i--){
    for(int j=7; j>=0; j--){
      double_pt(x3, y3, z3, x3, y3, z3);
      if((s1[i]>>j)&0x1){
        add_pt_tot(x3, y3, z3, x3, y3, z3, x1, y1, one);
      }
      if((s2[i]>>j)&0x1){
        add_pt_tot(x3, y3, z3, x3, y3, z3, x2, y2, one);
      }
    }
  }
}
/* Publically visible functions */
void
p521_32_scalarmult(unsigned char q[132], const unsigned char n[66], const unsigned char p[132]){
  felem xin;
  felem yin;
  felem x2;
  felem y2;
  felem z2;
  felem xout;
  felem yout;
  unpack(xin, p);
  unpack(yin, p+66);
  scalarmult(x2, y2, z2, xin, yin, n);
  to_affine(xout, yout, x2, y2, z2);
  pack(q, xout);
  pack(q+66, yout);
}

void
p521_32_scalarmult_base(unsigned char q[132], const unsigned char n[66]){
  felem x2;
  felem y2;
  felem z2;
  felem xout;
  felem yout;
  scalarmult(x2, y2, z2, base_x, base_y, n);
  to_affine(xout, yout, x2, y2, z2);
  pack(q, xout);
  pack(q+66, yout);
}

void
p521_32_double_scalarmult_base(unsigned char *q, const unsigned char a[132], const unsigned char s1[66], const unsigned char s2[66]){
  felem x2,y2;
  felem x3, y3, z3;
  felem xout, yout;
  unpack(x2, a);
  unpack(y2, a+66);
  double_scalarmult(x3, y3, z3, s1, base_x, base_y, s2, x2, y2);
  to_affine(xout, yout, x3, y3, z3);
  pack(q, xout);
  pack(q+66, yout);
}

bool
p521_32_valid(const unsigned char p[132]){
  felem x;
  felem y;
  felem one={1};
  unpack(x, p);
  unpack(y, p+66);
  return oncurve(x, y, one);
}
