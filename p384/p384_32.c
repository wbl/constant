/* Copyright (c) Watson Ladd (Mozilla) 2016 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

/* A constant time 32 bit implementation of P384             *
 * We use 64 bit words in our multiply and addition routines *
 * Can replace with assembler intrinsics. Heck, can do the   *
 * whole thing with assembler */

#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include "p384_32.h"

/* Constants */
/* We use little-endian arrays */
static const uint32_t prime[12] = { 0xffffffff, 0x0,        0x0,
                                    0xffffffff, 0xfffffffe, 0xffffffff,
                                    0xffffffff, 0xffffffff, 0xffffffff,
                                    0xffffffff, 0xffffffff, 0xffffffff };
static const uint32_t primes2[12] = { 0xfffffffd, 0x0,        0x0,
                                      0xffffffff, 0xfffffffe, 0xffffffff,
                                      0xffffffff, 0xffffffff, 0xffffffff,
                                      0xffffffff, 0xffffffff, 0xffffffff };
static uint64_t mask_lo = 0x00000000ffffffff;

static const uint32_t Rsqr[12] = { 0x1, 0xfffffffe, 0x0, 0x2, 0x0, 0xfffffffe,
                                   0x0, 0x2,        0x1, 0x0, 0x0, 0x0 };
static const uint32_t R[12] = { 0x1, 0xffffffff, 0xffffffff, 0x0, 0x1, 0x0,
                                0x0, 0x0,        0x0,        0x0, 0x0, 0x0 };

static const uint32_t curve_b[12] = { 0xd3ec2aef, 0x2a85c8ed, 0x8a2ed19d,
                                      0xc656398d, 0x5013875a, 0x314088f,
                                      0xfe814112, 0x181d9c6e, 0xe3f82d19,
                                      0x988e056b, 0xe23ee7e4, 0xb3312fa7 };
static const uint32_t base_x[12] = { 0x72760ab7, 0x3a545e38, 0xbf55296c,
                                     0x5502f25d, 0x82542a38, 0x59f741e0,
                                     0x8ba79b98, 0x6e1d3b62, 0xf320ad74,
                                     0x8eb1c71e, 0xbe8b0537, 0xaa87ca22 };
static const uint32_t base_y[12] = { 0x90ea0e5f, 0x7a431d7c, 0x1d7e819d,
                                     0xa60b1ce,  0xb5f0b8c0, 0xe9da3113,
                                     0x289a147c, 0xf8f41dbd, 0x9292dc29,
                                     0x5d9e98bf, 0x96262c6f, 0x3617de4a };
/* Arithmetic */
typedef uint32_t felem[12];

static void
reduce_add_sub(felem r, uint32_t carry)
{
  uint64_t t;
  uint32_t d[12];
  uint32_t b = 0;
  uint32_t pb = 0;
  uint32_t do_sub;
  uint32_t mask_sub;
  uint32_t mask_nosub;
  /* Now need to compare r and carry to prime, and if greater subtract in
   * constant time */
  for (int i = 0; i < 12; i++) {
    t = (uint64_t)prime[i] + pb;
    b = r[i] < t;
    t = r[i] - t + ((uint64_t)b << 32);
    d[i] = (uint32_t)t & mask_lo;
    pb = b;
  }
  /* It should be the case that we only potentially need one subtraction. So if
   * carry is set, should have pb set */
  /* Will do target tests (somehow: need to expose more internals. Or use test
   * routines here)*/
  do_sub = 1 - ((carry + pb) & 0x01);
  mask_sub = (uint32_t)-do_sub; // assume 2's complement
  mask_nosub = ~mask_sub;
  for (int i = 0; i < 12; i++) {
    r[i] = (mask_nosub & r[i]) | (mask_sub & d[i]);
  }
}

static void
add(felem r, const felem a, const felem b)
{
  uint32_t carry = 0;
  uint64_t t;
  /* This part should be done with add/adc or replaced with asm loop if we want
   * to go per-cpu */
  for (int i = 0; i < 12; i++) {
    t = (uint64_t)a[i] + (uint64_t)b[i] + carry;
    r[i] = (uint32_t)(t & mask_lo);
    carry = t >> 32;
  }
  reduce_add_sub(r, carry);
}

static void
sub(felem r, const felem a, const felem b)
{ /* Will need testing*/
  uint32_t carry = 0;
  uint64_t t = 0;
  uint32_t brw = 0;
  uint32_t pbrw = 0;
  for (int i = 0; i < 12; i++) { /* Assembler would be great for this.*/
    t = (uint64_t)prime[i] + a[i] + carry;
    brw = t < ((uint64_t)b[i]) + pbrw;
    t += ((uint64_t)brw) << 32;
    t -= (uint64_t)b[i] + (uint64_t)pbrw;
    r[i] = (uint32_t)(t & mask_lo);
    carry = t >> 32;
    pbrw = brw;
  }
  reduce_add_sub(r, carry);
}

static void
prod_red(felem r, uint32_t p[24])
{
  uint64_t t;
  uint32_t carry;
  uint32_t delayed[13] = { 0 };
  uint32_t m;
  for (int i = 0; i < 12; i++) {
    m = p[i];
    carry = 0;
    for (int j = 0; j < 12;
         j++) { /* This adds a multiple of prime that makes p[i] zero */
      t = (uint64_t)p[i + j] + ((uint64_t)m) * prime[j] + carry;
      p[i + j] = (uint32_t)(t & mask_lo);
      carry = t >> 32;
    }
    delayed[i] = carry;
  }
  carry = 0;
  for (int i = 0; i < 12; i++) {
    t = ((uint64_t)p[i + 12]) + carry + delayed[i];
    r[i] = t & mask_lo;
    carry = t >> 32;
  }
  reduce_add_sub(r, delayed[12] + carry);
}

/* Question: how to multiply by 2, 3, and 8? A: 2 is easy, as is 3. For 8
 * multiply by 2 four times*/
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
mult_nored(uint32_t prod[24], const felem a, const felem b)
{
  uint64_t t;
  uint32_t carry;
  for (int i = 0; i < 24; i++) {
    prod[i] = 0;
  }
  for (int i = 0; i < 12; i++) { /*TODO: Karastuba?*/
    carry = 0;
    for (int j = 0; j < 12; j++) {
      t = ((uint64_t)a[i]) * b[j] + carry + prod[i + j];
      prod[i + j] = (uint32_t)(t & mask_lo);
      carry = t >> 32;
    }
    prod[12 + i] = carry;
  }
}

static void
mult(felem r, const felem a, const felem b)
{
  uint32_t prod[24];
  mult_nored(prod, a, b);
  prod_red(r, prod);
}

static void
sqr(felem r, const felem a)
{ /* Doesn't seem to help very much*/
  uint32_t prod[24];
  uint64_t t;
  uint32_t carry;
  for (int i = 0; i < 24; i++) {
    prod[i] = 0;
  }

  for (int i = 0; i < 12; i++) {
    carry = 0;
    for (int j = i + 1; j < 12; j++) {
      t = ((uint64_t)a[i]) * a[j] + carry + prod[i + j];
      prod[i + j] = (uint32_t)(t & mask_lo);
      carry = t >> 32;
    }
    prod[12 + i] = carry;
  }
  carry = 0;
  for (int i = 0; i < 24; i++) {
    t = ((uint64_t)prod[i]) * 2 + carry;
    prod[i] = (uint32_t)t;
    carry = t >> 32;
  }
  carry = 0;
  for (int i = 0; i < 12; i++) {
    t = ((uint64_t)a[i]) * a[i] + carry + prod[2 * i];
    prod[2 * i] = t & mask_lo;
    carry = t >> 32;
    t = ((uint64_t)prod[2 * i + 1]) + carry;
    prod[2 * i + 1] = t & mask_lo;
    carry = t >> 32;
  }
  prod_red(r, prod);
}

/* Now for some packing and unpacking */
/* These don't do conversion */
static void
pack(unsigned char* out, const felem r)
{ /*Big endian*/
  for (int i = 0; i < 12; i++) {
    out[4 * (11 - i) + 3] = r[i] & 0xff;
    out[4 * (11 - i) + 2] = (r[i] >> 8) & 0xff;
    out[4 * (11 - i) + 1] = (r[i] >> 16) & 0xff;
    out[4 * (11 - i)] = (r[i] >> 24) & 0xff;
  }
}

static void
unpack(felem r, const unsigned char* in)
{
  for (int i = 0; i < 12; i++) {
    r[i] = in[4 * (11 - i)] << 24 | in[4 * (11 - i) + 1] << 16 |
           in[4 * (11 - i) + 2] << 8 | in[4 * (11 - i) + 3];
  }
}

static void
to_mont(felem r, const felem a)
{
  mult(r, a, Rsqr);
}

static void
from_mont(felem r, const felem a)
{
  felem one = { 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 };
  mult(r, a, one);
}

static void
mov(felem r, const felem a)
{
  for (int i = 0; i < 12; i++) {
    r[i] = a[i];
  }
}

/* And we need to invert in the field via CRT. */

static void
inv(felem r, const felem a)
{ /* Cannot be in place */
  /* Use an addition chain */
  felem thirteen;
  felem sixty3;
  felem twelve;
  felem asqr;
  felem two32sub3;
  felem two32sub1;
  felem tmp;
  sqr(r, a);
  mov(asqr, r);
  mult(r, r, a);
  sqr(r, r);
  sqr(r, r);
  mov(twelve, r);
  mult(r, r, a);
  mov(thirteen, r);
  mult(r, r, twelve);
  sqr(r, r);
  mult(r, r, thirteen);
  mov(sixty3, r);
  for(int i=0; i<6; i++){
    sqr(r, r);
  }
  mult(r, r, sixty3);
  for(int i=0; i<4; i++){
    sqr(r, r);
  }
  mult(r, r, thirteen);
  /* r is now 2^16-3. */
  mov(tmp, r);
  mult(r, r, asqr);
  for(int i=0; i<16; i++){
    sqr(r, r);
  }
  mult(r, r, tmp);
  mov(two32sub3, r);
  mult(r, r, a); //r is 2^32-2
  mult(tmp, r, a); //tmp is now 2^32-1
  mov(two32sub1, tmp);
  for(int i=0; i<32; i++){
    sqr(tmp, tmp);
  }
  mult(r, tmp, r); //2^64-2
  mult(tmp, r, a); //tmp 2^64-1
  for(int i=0; i<64; i++){
    sqr(tmp, tmp);
  }
  mult(r, tmp, r); //2^128-2
  mult(tmp, r, a); //tmp 2^128-1
  for(int i=0; i<128; i++){
    sqr(tmp, tmp);
  }
  mult(r, tmp, r); //2^256-2
  for(int i=0; i<32; i++){
    sqr(r, r);
  } //2^32(2^256-2)=2^288-2^33
  mult(r, r, two32sub1); //2^288-2^32-1
  for(int i=0; i<96; i++){
    sqr(r, r);
  }
  mult(r, r, two32sub3);
}

static bool
equal(const felem a, const felem b)
{ // Can leak *result*
  uint32_t diff = 0;
  for (int i = 0; i < 12; i++) {
    diff |= a[i] ^ b[i];
  }
  return diff == 0;
}

static bool
iszero(const felem a)
{
  uint32_t test = 0;
  for (int i = 0; i < 12; i++) {
    test |= a[i];
  }
  return test == 0;
}

static void
neg_conditional(felem r, const felem a, uint32_t cond)
{ /* Should try in-place*/
  uint32_t diff[12];
  uint32_t pbrw = 0;
  uint32_t brw = 0;
  uint64_t t;
  uint32_t mask_diff;
  uint32_t mask_nodiff;
  for (int i = 0; i < 12; i++) {
    t = (uint64_t)prime[i];
    brw = t < (uint64_t)a[i] + pbrw;
    t += (uint64_t)brw << 32;
    t -= (uint64_t)a[i] + pbrw;
    pbrw = brw;
    diff[i] = (uint32_t)(t & mask_lo); /* There is no carry because a<prime */
  }
  mask_diff = (uint32_t)-cond;
  mask_nodiff = ~mask_diff;
  for (int i = 0; i < 12; i++) {
    r[i] = (diff[i] & mask_diff) | (a[i] & mask_nodiff);
  }
}

static void
cmov(felem r, const felem a, uint32_t cond)
{
  uint32_t mask_set;
  uint32_t mask_unset;
  mask_set = (uint32_t)-cond;
  mask_unset = ~mask_set;
  for (int i = 0; i < 12; i++) {
    r[i] = (r[i] & mask_unset) | (a[i] & mask_set);
  }
}

/* Operations on the curve in Jacobian coordinates using readditions */
/* We do not implement a specialized affine addition because inversion is slow
 * (can fix) */
/* The point at infinity is exceptional and leaks. To deal with this we use a
 * signed form of exponents*/

static bool
oncurve(const felem x, const felem y, const felem z, bool not_mont)
{ // not montgomery
  felem z2, z4, z6, t0, t1, t2, t3, t4, t5, ysqr, rhs, bmont, xm, ym, zm;
  to_mont(bmont, curve_b);
  if (not_mont) {
    to_mont(xm, x);
    to_mont(ym, y);
    to_mont(zm, z);
  } else {
    mov(xm, x);
    mov(ym, y);
    mov(zm, z);
  }
  mult(z2, zm, zm);
  mult(z4, z2, z2);
  mult(z6, z4, z2);
  mult(t0, bmont, z6);
  mult(t1, xm, z4);
  mul3(t2, t1);
  mult(t3, xm, xm);
  mult(t4, t3, xm);
  sub(t5, t4, t2);
  add(rhs, t5, t0);
  mult(ysqr, ym, ym);
  return equal(ysqr, rhs);
}

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
      mov(x3, R);
      mov(y3, R);
      for(int i=0; i<12; i++){
	z3[i]=0;
      }
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
      mov(x3, R);
      mov(y3, R);
      for(int i=0; i<12; i++){
	z3[i]=0;
      }
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
add_pt_aff(felem x3, felem y3, felem z3, const felem x1, const felem y1,
               const felem z1, const felem x2, const felem y2)
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
  mov(u1, x1);
  mult(u2, z1z1, x2);
  mov(s1, y1);
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
  add(t11, z1, R);
  sqr(t12, t11);
  sub(t13, t12, z1z1);
  sub(t14, t13, R);
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

static void
recode(int out_d[77], int out_s[77], const unsigned char key[48])
{
  /* We use a signed representation where digits are -15, -14,... 16 */
  /* Below encodes it in constant time */
  int word = 0;
  int bits = 0;
  int carry = 0;
  int sub = 0;
  int bit = 0;
  int k = 0;
  for (int i = 0; i < 48; i++) {
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
        k++;
        word = 0;
        bits = 0;
      }
    }
  }
  word = word + carry;
  out_d[76] = word;
  out_s[76] = 0;
}

static void
scalarmult(felem x_out, felem y_out, const felem x_in, const felem y_in,
           const unsigned char key[48])
{
  felem xm;
  felem ym;
  bool correct;
  /* Note, we need to make sure that the key is < order for correctness */
  /* Remember z==1, in montgomery form is R */
  to_mont(xm, x_in);
  to_mont(ym, y_in);
  felem xQ, yQ, zQ;
  felem xR, yR, zR;
  felem xT, yT, zT, zzT, zzzT;
  felem table[17][5];
  int recoded_index[77];
  int recoded_sign[77];
  recode(recoded_index, recoded_sign, key);
  for (int i = 0; i < 12; i++) {
    xQ[i] = 0;
    yQ[i] = 0;
    zQ[i] = 0;
  }
  mov(xQ, R);
  mov(yQ, R); // Q is pt at infinity
  mov(table[0][0], xQ);
  mov(table[0][1], yQ);
  mov(table[0][2], zQ);
  mov(table[0][3], zQ);
  mov(table[0][4], zQ);
  mov(table[1][0], xm);
  mov(table[1][1], ym);
  mov(table[1][2], R);
  sqr(table[1][3], table[1][2]);
  mult(table[1][4], table[1][2], table[1][3]);
  for (int i = 2; i < 17; i++) {
    if (i % 2 == 1) {
      add_pt_aff(table[i][0], table[i][1], table[i][2], table[i - 1][0],
                     table[i - 1][1], table[i - 1][2], xm, ym);
    } else {
      double_pt(table[i][0], table[i][1], table[i][2], table[i / 2][0],
                table[i / 2][1], table[i / 2][2]);
    }
    sqr(table[i][3], table[i][2]);
    mult(table[i][4], table[i][3], table[i][2]);
  }
  bool first = 1;
  bool seen_1 = 0;
  for (int i = 76; i >= 0; i--) {
    if (!first) {
      double_pt(xQ, yQ, zQ, xQ, yQ, zQ);
      double_pt(xQ, yQ, zQ, xQ, yQ, zQ);
      double_pt(xQ, yQ, zQ, xQ, yQ, zQ);
      double_pt(xQ, yQ, zQ, xQ, yQ, zQ);
      double_pt(xQ, yQ, zQ, xQ, yQ, zQ);
    }
    first = 0;
    int sign = recoded_sign[i];
    int index = recoded_index[i];
    int valid_point = (index != 0); // check constant time
    for (int k = 0; k < 17; k++) {
      cmov(xT, table[k][0], k == index);
      cmov(yT, table[k][1], k == index);
      cmov(zT, table[k][2], k == index);
      cmov(zzT, table[k][3], k == index);
      cmov(zzzT, table[k][4], k == index);
    }
    neg_conditional(yT, yT, sign);
    readd_pt_const(xR, yR, zR, xQ, yQ, zQ, xT, yT, zT, zzT, zzzT);
    cmov(xR, xT, (1 - seen_1));
    cmov(yR, yT, (1 - seen_1));
    cmov(zR, zT, (1 - seen_1));
    seen_1 = seen_1 | valid_point;
    cmov(xQ, xR, valid_point);
    cmov(yQ, yR, valid_point);
    cmov(zQ, zR, valid_point);
  }
  to_affine(x_out, y_out, xQ, yQ, zQ);
  from_mont(x_out, x_out);
  from_mont(y_out, y_out);
}

static void
scalarmult_double(felem x, felem y, const felem x1, const felem y1, const unsigned char *s1, const felem x2, const felem y2, const unsigned char *s2){
  felem xQ, yQ, zQ;
  felem yT;
  felem x1m, y1m, x2m, y2m;
  int r_d1[77];
  int r_s1[77];
  int r_d2[77];
  int r_s2[77];
  felem table1[17][5];
  felem table2[17][5];
  to_mont(x1m, x1);
  to_mont(x2m, x2);
  to_mont(y1m, y1);
  to_mont(y2m, y2);
  for(int i=0; i<12; i++){
    zQ[i]=0;
  }
  mov(xQ, R);
  mov(yQ, R);
  mov(table1[0][0], xQ);
  mov(table2[0][0], xQ);
  mov(table1[0][1], yQ);
  mov(table2[0][1], yQ);
  mov(table1[0][2], zQ);
  mov(table2[0][2], zQ);
  mov(table1[0][3], zQ);
  mov(table2[0][3], zQ);
  mov(table1[0][4], zQ);
  mov(table2[0][4], zQ);
  mov(table1[1][0], x1m);
  mov(table1[1][1], y1m);
  mov(table1[1][2], R);
  mov(table1[1][3], R);
  mov(table1[1][4], R);
  mov(table2[1][0], x2m);
  mov(table2[1][1], y2m);
  mov(table2[1][2], R);
  mov(table2[1][3], R);
  mov(table2[1][4], R);
  for (int i = 2; i < 17; i++) {
    if (i % 2 == 1) {
      add_pt_const(table1[i][0], table1[i][1], table1[i][2], table1[i - 1][0],
                   table1[i - 1][1], table1[i - 1][2], x1m, y1m, R);
       add_pt_const(table2[i][0], table2[i][1], table2[i][2], table2[i - 1][0],
                   table2[i - 1][1], table2[i - 1][2], x2m, y2m, R);
    } else {
      double_pt(table1[i][0], table1[i][1], table1[i][2], table1[i / 2][0],
                table1[i / 2][1], table1[i / 2][2]);
      double_pt(table2[i][0], table2[i][1], table2[i][2], table2[i / 2][0],
		table2[i / 2][1], table2[i / 2][2]);
    }
    sqr(table1[i][3], table1[i][2]);
    mult(table1[i][4], table1[i][3], table1[i][2]);
    sqr(table2[i][3], table2[i][2]);
    mult(table2[i][4], table2[i][3], table2[i][2]);
    
  }
  recode(r_d1, r_s1, s1);
  recode(r_d2, r_s2, s2);
  int first = 1;
  for(int i=76; i>=0; i--){
    if(!first){
      double_pt(xQ, yQ, zQ, xQ, yQ, zQ);
      double_pt(xQ, yQ, zQ, xQ, yQ, zQ);
      double_pt(xQ, yQ, zQ, xQ, yQ, zQ);
      double_pt(xQ, yQ, zQ, xQ, yQ, zQ);
      double_pt(xQ, yQ, zQ, xQ, yQ, zQ);
    }
    if(r_d1[i]){
      mov(yT, table1[r_d1[i]][1]);
      neg_conditional(yT, yT, r_s1[i]);
      readd_pt_tot(xQ, yQ, zQ, xQ, yQ, zQ, table1[r_d1[i]][0], yT, table1[r_d1[i]][2], table1[r_d1[i]][3], table1[r_d1[i]][4]);
    }
    if(r_d2[i]){
      mov(yT, table2[r_d2[i]][1]);
      neg_conditional(yT, yT, r_s2[i]);
      readd_pt_tot(xQ, yQ, zQ, xQ, yQ, zQ, table2[r_d2[i]][0], yT, table2[r_d2[i]][2], table2[r_d2[i]][3], table2[r_d2[i]][4]);
    }
    first = 0;
  }
  to_affine(x, y, xQ, yQ, zQ);
  from_mont(x, x);
  from_mont(y, y);
}

/* Interface to outside world */
bool
p384_32_valid(unsigned char p[96])
{
  felem x;
  felem y;
  felem one = { 1 };
  unpack(x, p);
  unpack(y, p + 48);
  return oncurve(x, y, one, true);
}

void
p384_32_scalarmult(unsigned char q[96], const unsigned char n[48],
                   const unsigned char p[96])
{
  felem x;
  felem y;
  felem x_t;
  felem y_t;
  unpack(x, p);
  unpack(y, p + 48);
  felem one = { 1 };
  scalarmult(x_t, y_t, x, y, n);
  pack(q, x_t);
  pack(q + 48, y_t);
}

void
p384_32_scalarmult_base(unsigned char q[96], const unsigned char n[48])
{
  felem x;
  felem y;
  scalarmult(x, y, base_x, base_y, n);
  pack(q, x);
  pack(q + 48, y);
}

void
p384_32_double_scalarmult_base(unsigned char q[96], const unsigned char a[96], const unsigned char n1[48], const unsigned char n2[48]){
  felem x_a;
  felem y_a;
  felem x;
  felem y;
  unpack(x_a, a);
  unpack(y_a, a+48);
  scalarmult_double(x, y, base_x, base_y, n1, x_a, y_a, n2);
  pack(q, x);
  pack(q+48, y);
}
