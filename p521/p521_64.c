/* Gutted and attached to NSS by Watson Ladd (Mozilla)
 * in 2016
 */

/*
 * Written by Adam Langley (Google) for the OpenSSL project
 */

/* Copyright 2011 Google Inc.
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
*/

/*
 * A 64-bit implementation of the NIST P-521 elliptic curve point multiplication
 *
 * OpenSSL integration was taken from Emilia Kasper's work in ecp_nistp224.c.
 * Otherwise based on Emilia's P224 work, which was inspired by my curve25519
 * work which got its smarts from Daniel J. Bernstein's work on the same.
 */
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include "p521_64.h"
/* even with gcc, the typedef won't work for 32-bit platforms */
typedef __uint128_t
  uint128_t; /* nonstandard; implemented by gcc on 64-bit platforms */

typedef uint8_t u8;
typedef uint64_t u64;
typedef int64_t s64;

/* The underlying field.
 *
 * P521 operates over GF(2^521-1). We can serialise an element of this field
 * into 66 bytes where the most significant byte contains only a single bit. We
 * call this an felem_bytearray. */

typedef u8 felem_bytearray[66];

/* These are the parameters of P521, taken from FIPS 186-3, section D.1.2.5.
 * These values are big-endian. */
static const felem_bytearray nistp521_curve_params[5] = {
  { 0x01, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, /* p */
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff },
  { 0x01, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, /* a = -3 */
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfc },
  { 0x00, 0x51, 0x95, 0x3e, 0xb9, 0x61, 0x8e, 0x1c, /* b */
    0x9a, 0x1f, 0x92, 0x9a, 0x21, 0xa0, 0xb6, 0x85, 0x40, 0xee, 0xa2, 0xda,
    0x72, 0x5b, 0x99, 0xb3, 0x15, 0xf3, 0xb8, 0xb4, 0x89, 0x91, 0x8e, 0xf1,
    0x09, 0xe1, 0x56, 0x19, 0x39, 0x51, 0xec, 0x7e, 0x93, 0x7b, 0x16, 0x52,
    0xc0, 0xbd, 0x3b, 0xb1, 0xbf, 0x07, 0x35, 0x73, 0xdf, 0x88, 0x3d, 0x2c,
    0x34, 0xf1, 0xef, 0x45, 0x1f, 0xd4, 0x6b, 0x50, 0x3f, 0x00 },
  { 0x00, 0xc6, 0x85, 0x8e, 0x06, 0xb7, 0x04, 0x04, /* x */
    0xe9, 0xcd, 0x9e, 0x3e, 0xcb, 0x66, 0x23, 0x95, 0xb4, 0x42, 0x9c, 0x64,
    0x81, 0x39, 0x05, 0x3f, 0xb5, 0x21, 0xf8, 0x28, 0xaf, 0x60, 0x6b, 0x4d,
    0x3d, 0xba, 0xa1, 0x4b, 0x5e, 0x77, 0xef, 0xe7, 0x59, 0x28, 0xfe, 0x1d,
    0xc1, 0x27, 0xa2, 0xff, 0xa8, 0xde, 0x33, 0x48, 0xb3, 0xc1, 0x85, 0x6a,
    0x42, 0x9b, 0xf9, 0x7e, 0x7e, 0x31, 0xc2, 0xe5, 0xbd, 0x66 },
  { 0x01, 0x18, 0x39, 0x29, 0x6a, 0x78, 0x9a, 0x3b, /* y */
    0xc0, 0x04, 0x5c, 0x8a, 0x5f, 0xb4, 0x2c, 0x7d, 0x1b, 0xd9, 0x98, 0xf5,
    0x44, 0x49, 0x57, 0x9b, 0x44, 0x68, 0x17, 0xaf, 0xbd, 0x17, 0x27, 0x3e,
    0x66, 0x2c, 0x97, 0xee, 0x72, 0x99, 0x5e, 0xf4, 0x26, 0x40, 0xc5, 0x50,
    0xb9, 0x01, 0x3f, 0xad, 0x07, 0x61, 0x35, 0x3c, 0x70, 0x86, 0xa2, 0x72,
    0xc2, 0x40, 0x88, 0xbe, 0x94, 0x76, 0x9f, 0xd1, 0x66, 0x50 }
};

/* The representation of field elements.
 * ------------------------------------
 *
 * We represent field elements with nine values. These values are either 64 or
 * 128 bits and the field element represented is:
 *   v[0]*2^0 + v[1]*2^58 + v[2]*2^116 + ... + v[8]*2^464  (mod p)
 * Each of the nine values is called a 'limb'. Since the limbs are spaced only
 * 58 bits apart, but are greater than 58 bits in length, the most significant
 * bits of each limb overlap with the least significant bits of the next.
 *
 * A field element with 64-bit limbs is an 'felem'. One with 128-bit limbs is a
 * 'largefelem' */

#define NLIMBS 9

typedef uint64_t limb;
typedef limb felem[NLIMBS];
typedef uint128_t largefelem[NLIMBS];

static const limb bottom57bits = 0x1ffffffffffffff;
static const limb bottom58bits = 0x3ffffffffffffff;

static limb
load(const u8* where)
{
  limb t = 0;
  int i = 0;
  for (i = 7; i >= 0; i--) {
    t <<= 8;
    t |= where[i];
  }
  return t;
}

static void
orin(u8* where, const limb what)
{
  limb t = load(where);
  t |= what;
  for (int i = 0; i < 8; i++) {
    where[i] = t & 0xff;
    t >>= 8;
  }
}

/* bin66_to_felem takes a little-endian byte array and converts it into felem
 * form. This assumes that the CPU is little-endian. */
static void bin66_to_felem(felem out, const u8 in[66]) /* XXX */
{
  out[0] = load(&in[0]) & bottom58bits;
  out[1] = (load(&in[7]) >> 2) & bottom58bits;
  out[2] = (load(&in[14]) >> 4) & bottom58bits;
  out[3] = (load(&in[21]) >> 6) & bottom58bits;
  out[4] = (load(&in[29])) & bottom58bits;
  out[5] = (load(&in[36]) >> 2) & bottom58bits;
  out[6] = (load(&in[43]) >> 4) & bottom58bits;
  out[7] = (load(&in[50]) >> 6) & bottom58bits;
  out[8] = (load(&in[58])) & bottom57bits;
}

/* felem_to_bin66 takes an felem and serialises into a little endian, 66 byte
 * array. This assumes that the CPU is little-endian. */
static void felem_to_bin66(u8 out[66], const felem in) /* XXX */
{
  memset(out, 0, 66);
  orin(out, in[0]);
  orin(out+7, in[1] << 2);
  orin(out+14, in[2] << 4);
  orin(out+21, in[3] << 6);
  orin(out+29,in[4]);
  orin(out+36, in[5] << 2);
  orin(out+43, in[6] << 4);
  orin(out+50, in[7] << 6);
  orin(out+58, in[8]);
}

static void
flip_endian(u8* out, const u8* in, unsigned len)
{
  unsigned i;
  for (i = 0; i < len; ++i)
    out[i] = in[len - 1 - i];
}

/* To preserve endianness when eating points */

/* Field operations
 * ---------------- */

static void
felem_one(felem out)
{
  out[0] = 1;
  out[1] = 0;
  out[2] = 0;
  out[3] = 0;
  out[4] = 0;
  out[5] = 0;
  out[6] = 0;
  out[7] = 0;
  out[8] = 0;
}

static void
felem_assign(felem out, const felem in)
{
  out[0] = in[0];
  out[1] = in[1];
  out[2] = in[2];
  out[3] = in[3];
  out[4] = in[4];
  out[5] = in[5];
  out[6] = in[6];
  out[7] = in[7];
  out[8] = in[8];
}

/* felem_sum64 sets out = out + in. */
static void
felem_sum64(felem out, const felem in)
{
  out[0] += in[0];
  out[1] += in[1];
  out[2] += in[2];
  out[3] += in[3];
  out[4] += in[4];
  out[5] += in[5];
  out[6] += in[6];
  out[7] += in[7];
  out[8] += in[8];
}

/* felem_scalar sets out = in * scalar */
static void
felem_scalar(felem out, const felem in, limb scalar)
{
  out[0] = in[0] * scalar;
  out[1] = in[1] * scalar;
  out[2] = in[2] * scalar;
  out[3] = in[3] * scalar;
  out[4] = in[4] * scalar;
  out[5] = in[5] * scalar;
  out[6] = in[6] * scalar;
  out[7] = in[7] * scalar;
  out[8] = in[8] * scalar;
}

/* felem_scalar64 sets out = out * scalar */
static void
felem_scalar64(felem out, limb scalar)
{
  out[0] *= scalar;
  out[1] *= scalar;
  out[2] *= scalar;
  out[3] *= scalar;
  out[4] *= scalar;
  out[5] *= scalar;
  out[6] *= scalar;
  out[7] *= scalar;
  out[8] *= scalar;
}

/* felem_scalar128 sets out = out * scalar */
static void
felem_scalar128(largefelem out, limb scalar)
{
  out[0] *= scalar;
  out[1] *= scalar;
  out[2] *= scalar;
  out[3] *= scalar;
  out[4] *= scalar;
  out[5] *= scalar;
  out[6] *= scalar;
  out[7] *= scalar;
  out[8] *= scalar;
}

/* felem_neg sets |out| to |-in|
 * On entry:
 *   in[i] < 2^59 + 2^14
 * On exit:
 *   out[i] < 2^62
 */
static void
felem_neg(felem out, const felem in)
{
  /* In order to prevent underflow, we subtract from 0 mod p. */
  static const limb two62m3 = (((limb)1) << 62) - (((limb)1) << 5);
  static const limb two62m2 = (((limb)1) << 62) - (((limb)1) << 4);

  out[0] = two62m3 - in[0];
  out[1] = two62m2 - in[1];
  out[2] = two62m2 - in[2];
  out[3] = two62m2 - in[3];
  out[4] = two62m2 - in[4];
  out[5] = two62m2 - in[5];
  out[6] = two62m2 - in[6];
  out[7] = two62m2 - in[7];
  out[8] = two62m2 - in[8];
}

/* felem_diff64 subtracts |in| from |out|
 * On entry:
 *   in[i] < 2^59 + 2^14
 * On exit:
 *   out[i] < out[i] + 2^62
 */
static void
felem_diff64(felem out, const felem in)
{
  /* In order to prevent underflow, we add 0 mod p before subtracting. */
  static const limb two62m3 = (((limb)1) << 62) - (((limb)1) << 5);
  static const limb two62m2 = (((limb)1) << 62) - (((limb)1) << 4);

  out[0] += two62m3 - in[0];
  out[1] += two62m2 - in[1];
  out[2] += two62m2 - in[2];
  out[3] += two62m2 - in[3];
  out[4] += two62m2 - in[4];
  out[5] += two62m2 - in[5];
  out[6] += two62m2 - in[6];
  out[7] += two62m2 - in[7];
  out[8] += two62m2 - in[8];
}

/* felem_diff_128_64 subtracts |in| from |out|
 * On entry:
 *   in[i] < 2^62 + 2^17
 * On exit:
 *   out[i] < out[i] + 2^63
 */
static void
felem_diff_128_64(largefelem out, const felem in)
{
  /* In order to prevent underflow, we add 0 mod p before subtracting. */
  static const limb two63m6 = (((limb)1) << 62) - (((limb)1) << 5);
  static const limb two63m5 = (((limb)1) << 62) - (((limb)1) << 4);

  out[0] += two63m6 - in[0];
  out[1] += two63m5 - in[1];
  out[2] += two63m5 - in[2];
  out[3] += two63m5 - in[3];
  out[4] += two63m5 - in[4];
  out[5] += two63m5 - in[5];
  out[6] += two63m5 - in[6];
  out[7] += two63m5 - in[7];
  out[8] += two63m5 - in[8];
}

/* felem_diff_128_64 subtracts |in| from |out|
 * On entry:
 *   in[i] < 2^126
 * On exit:
 *   out[i] < out[i] + 2^127 - 2^69
 */
static void
felem_diff128(largefelem out, const largefelem in)
{
  /* In order to prevent underflow, we add 0 mod p before subtracting. */
  static const uint128_t two127m70 =
    (((uint128_t)1) << 127) - (((uint128_t)1) << 70);
  static const uint128_t two127m69 =
    (((uint128_t)1) << 127) - (((uint128_t)1) << 69);

  out[0] += (two127m70 - in[0]);
  out[1] += (two127m69 - in[1]);
  out[2] += (two127m69 - in[2]);
  out[3] += (two127m69 - in[3]);
  out[4] += (two127m69 - in[4]);
  out[5] += (two127m69 - in[5]);
  out[6] += (two127m69 - in[6]);
  out[7] += (two127m69 - in[7]);
  out[8] += (two127m69 - in[8]);
}

/* felem_square sets |out| = |in|^2
 * On entry:
 *   in[i] < 2^62
 * On exit:
 *   out[i] < 17 * max(in[i]) * max(in[i])
 */
static void
felem_square(largefelem out, const felem in)
{
  felem inx2, inx4;
  felem_scalar(inx2, in, 2);
  felem_scalar(inx4, in, 4);

  /* We have many cases were we want to do
   *   in[x] * in[y] +
   *   in[y] * in[x]
   * This is obviously just
   *   2 * in[x] * in[y]
   * However, rather than do the doubling on the 128 bit result, we
   * double one of the inputs to the multiplication by reading from
   * |inx2| */

  out[0] = ((uint128_t)in[0]) * in[0];
  out[1] = ((uint128_t)in[0]) * inx2[1];
  out[2] = ((uint128_t)in[0]) * inx2[2] + ((uint128_t)in[1]) * in[1];
  out[3] = ((uint128_t)in[0]) * inx2[3] + ((uint128_t)in[1]) * inx2[2];
  out[4] = ((uint128_t)in[0]) * inx2[4] + ((uint128_t)in[1]) * inx2[3] +
           ((uint128_t)in[2]) * in[2];
  out[5] = ((uint128_t)in[0]) * inx2[5] + ((uint128_t)in[1]) * inx2[4] +
           ((uint128_t)in[2]) * inx2[3];
  out[6] = ((uint128_t)in[0]) * inx2[6] + ((uint128_t)in[1]) * inx2[5] +
           ((uint128_t)in[2]) * inx2[4] + ((uint128_t)in[3]) * in[3];
  out[7] = ((uint128_t)in[0]) * inx2[7] + ((uint128_t)in[1]) * inx2[6] +
           ((uint128_t)in[2]) * inx2[5] + ((uint128_t)in[3]) * inx2[4];
  out[8] = ((uint128_t)in[0]) * inx2[8] + ((uint128_t)in[1]) * inx2[7] +
           ((uint128_t)in[2]) * inx2[6] + ((uint128_t)in[3]) * inx2[5] +
           ((uint128_t)in[4]) * in[4];

  /* The remaining limbs fall above 2^521, with the first falling at
   * 2^522. They correspond to locations one bit up from the limbs
   * produced above so we would have to multiply by two to align them.
   * Again, rather than operate on the 128-bit result, we double one of
   * the inputs to the multiplication. If we want to double for both this
   * reason, and the reason above, then we end up multiplying by four. */

  /* 9 */
  out[0] += ((uint128_t)in[1]) * inx4[8] + ((uint128_t)in[2]) * inx4[7] +
            ((uint128_t)in[3]) * inx4[6] + ((uint128_t)in[4]) * inx4[5];

  /* 10 */
  out[1] += ((uint128_t)in[2]) * inx4[8] + ((uint128_t)in[3]) * inx4[7] +
            ((uint128_t)in[4]) * inx4[6] + ((uint128_t)in[5]) * inx2[5];

  /* 11 */
  out[2] += ((uint128_t)in[3]) * inx4[8] + ((uint128_t)in[4]) * inx4[7] +
            ((uint128_t)in[5]) * inx4[6];

  /* 12 */
  out[3] += ((uint128_t)in[4]) * inx4[8] + ((uint128_t)in[5]) * inx4[7] +
            ((uint128_t)in[6]) * inx2[6];

  /* 13 */
  out[4] += ((uint128_t)in[5]) * inx4[8] + ((uint128_t)in[6]) * inx4[7];

  /* 14 */
  out[5] += ((uint128_t)in[6]) * inx4[8] + ((uint128_t)in[7]) * inx2[7];

  /* 15 */
  out[6] += ((uint128_t)in[7]) * inx4[8];

  /* 16 */
  out[7] += ((uint128_t)in[8]) * inx2[8];
}

/* felem_mul sets |out| = |in1| * |in2|
 * On entry:
 *   in1[i] < 2^64
 *   in2[i] < 2^63
 * On exit:
 *   out[i] < 17 * max(in1[i]) * max(in2[i])
 */
static void
felem_mul(largefelem out, const felem in1, const felem in2)
{
  felem in2x2;
  felem_scalar(in2x2, in2, 2);

  out[0] = ((uint128_t)in1[0]) * in2[0];

  out[1] = ((uint128_t)in1[0]) * in2[1] + ((uint128_t)in1[1]) * in2[0];

  out[2] = ((uint128_t)in1[0]) * in2[2] + ((uint128_t)in1[1]) * in2[1] +
           ((uint128_t)in1[2]) * in2[0];

  out[3] = ((uint128_t)in1[0]) * in2[3] + ((uint128_t)in1[1]) * in2[2] +
           ((uint128_t)in1[2]) * in2[1] + ((uint128_t)in1[3]) * in2[0];

  out[4] = ((uint128_t)in1[0]) * in2[4] + ((uint128_t)in1[1]) * in2[3] +
           ((uint128_t)in1[2]) * in2[2] + ((uint128_t)in1[3]) * in2[1] +
           ((uint128_t)in1[4]) * in2[0];

  out[5] = ((uint128_t)in1[0]) * in2[5] + ((uint128_t)in1[1]) * in2[4] +
           ((uint128_t)in1[2]) * in2[3] + ((uint128_t)in1[3]) * in2[2] +
           ((uint128_t)in1[4]) * in2[1] + ((uint128_t)in1[5]) * in2[0];

  out[6] = ((uint128_t)in1[0]) * in2[6] + ((uint128_t)in1[1]) * in2[5] +
           ((uint128_t)in1[2]) * in2[4] + ((uint128_t)in1[3]) * in2[3] +
           ((uint128_t)in1[4]) * in2[2] + ((uint128_t)in1[5]) * in2[1] +
           ((uint128_t)in1[6]) * in2[0];

  out[7] = ((uint128_t)in1[0]) * in2[7] + ((uint128_t)in1[1]) * in2[6] +
           ((uint128_t)in1[2]) * in2[5] + ((uint128_t)in1[3]) * in2[4] +
           ((uint128_t)in1[4]) * in2[3] + ((uint128_t)in1[5]) * in2[2] +
           ((uint128_t)in1[6]) * in2[1] + ((uint128_t)in1[7]) * in2[0];

  out[8] = ((uint128_t)in1[0]) * in2[8] + ((uint128_t)in1[1]) * in2[7] +
           ((uint128_t)in1[2]) * in2[6] + ((uint128_t)in1[3]) * in2[5] +
           ((uint128_t)in1[4]) * in2[4] + ((uint128_t)in1[5]) * in2[3] +
           ((uint128_t)in1[6]) * in2[2] + ((uint128_t)in1[7]) * in2[1] +
           ((uint128_t)in1[8]) * in2[0];

  /* See comment in felem_square about the use of in2x2 here */

  out[0] += ((uint128_t)in1[1]) * in2x2[8] + ((uint128_t)in1[2]) * in2x2[7] +
            ((uint128_t)in1[3]) * in2x2[6] + ((uint128_t)in1[4]) * in2x2[5] +
            ((uint128_t)in1[5]) * in2x2[4] + ((uint128_t)in1[6]) * in2x2[3] +
            ((uint128_t)in1[7]) * in2x2[2] + ((uint128_t)in1[8]) * in2x2[1];

  out[1] += ((uint128_t)in1[2]) * in2x2[8] + ((uint128_t)in1[3]) * in2x2[7] +
            ((uint128_t)in1[4]) * in2x2[6] + ((uint128_t)in1[5]) * in2x2[5] +
            ((uint128_t)in1[6]) * in2x2[4] + ((uint128_t)in1[7]) * in2x2[3] +
            ((uint128_t)in1[8]) * in2x2[2];

  out[2] += ((uint128_t)in1[3]) * in2x2[8] + ((uint128_t)in1[4]) * in2x2[7] +
            ((uint128_t)in1[5]) * in2x2[6] + ((uint128_t)in1[6]) * in2x2[5] +
            ((uint128_t)in1[7]) * in2x2[4] + ((uint128_t)in1[8]) * in2x2[3];

  out[3] += ((uint128_t)in1[4]) * in2x2[8] + ((uint128_t)in1[5]) * in2x2[7] +
            ((uint128_t)in1[6]) * in2x2[6] + ((uint128_t)in1[7]) * in2x2[5] +
            ((uint128_t)in1[8]) * in2x2[4];

  out[4] += ((uint128_t)in1[5]) * in2x2[8] + ((uint128_t)in1[6]) * in2x2[7] +
            ((uint128_t)in1[7]) * in2x2[6] + ((uint128_t)in1[8]) * in2x2[5];

  out[5] += ((uint128_t)in1[6]) * in2x2[8] + ((uint128_t)in1[7]) * in2x2[7] +
            ((uint128_t)in1[8]) * in2x2[6];

  out[6] += ((uint128_t)in1[7]) * in2x2[8] + ((uint128_t)in1[8]) * in2x2[7];

  out[7] += ((uint128_t)in1[8]) * in2x2[8];
}

static const limb bottom52bits = 0xfffffffffffff;

/* felem_reduce converts a largefelem to an felem.
 * On entry:
 *   in[i] < 2^128
 * On exit:
 *   out[i] < 2^59 + 2^14
 */
static void
felem_reduce(felem out, const largefelem in)
{
  u64 overflow1, overflow2;

  out[0] = ((limb)in[0]) & bottom58bits;
  out[1] = ((limb)in[1]) & bottom58bits;
  out[2] = ((limb)in[2]) & bottom58bits;
  out[3] = ((limb)in[3]) & bottom58bits;
  out[4] = ((limb)in[4]) & bottom58bits;
  out[5] = ((limb)in[5]) & bottom58bits;
  out[6] = ((limb)in[6]) & bottom58bits;
  out[7] = ((limb)in[7]) & bottom58bits;
  out[8] = ((limb)in[8]) & bottom58bits;

  /* out[i] < 2^58 */

  out[1] += ((limb)in[0]) >> 58;
  out[1] += (((limb)(in[0] >> 64)) & bottom52bits) << 6;
  /* out[1] < 2^58 + 2^6 + 2^58
   *        = 2^59 + 2^6 */
  out[2] += ((limb)(in[0] >> 64)) >> 52;

  out[2] += ((limb)in[1]) >> 58;
  out[2] += (((limb)(in[1] >> 64)) & bottom52bits) << 6;
  out[3] += ((limb)(in[1] >> 64)) >> 52;

  out[3] += ((limb)in[2]) >> 58;
  out[3] += (((limb)(in[2] >> 64)) & bottom52bits) << 6;
  out[4] += ((limb)(in[2] >> 64)) >> 52;

  out[4] += ((limb)in[3]) >> 58;
  out[4] += (((limb)(in[3] >> 64)) & bottom52bits) << 6;
  out[5] += ((limb)(in[3] >> 64)) >> 52;

  out[5] += ((limb)in[4]) >> 58;
  out[5] += (((limb)(in[4] >> 64)) & bottom52bits) << 6;
  out[6] += ((limb)(in[4] >> 64)) >> 52;

  out[6] += ((limb)in[5]) >> 58;
  out[6] += (((limb)(in[5] >> 64)) & bottom52bits) << 6;
  out[7] += ((limb)(in[5] >> 64)) >> 52;

  out[7] += ((limb)in[6]) >> 58;
  out[7] += (((limb)(in[6] >> 64)) & bottom52bits) << 6;
  out[8] += ((limb)(in[6] >> 64)) >> 52;

  out[8] += ((limb)in[7]) >> 58;
  out[8] += (((limb)(in[7] >> 64)) & bottom52bits) << 6;
  /* out[x > 1] < 2^58 + 2^6 + 2^58 + 2^12
   *            < 2^59 + 2^13 */
  overflow1 = ((limb)(in[7] >> 64)) >> 52;

  overflow1 += ((limb)in[8]) >> 58;
  overflow1 += (((limb)(in[8] >> 64)) & bottom52bits) << 6;
  overflow2 = ((limb)(in[8] >> 64)) >> 52;

  overflow1 <<= 1; /* overflow1 < 2^13 + 2^7 + 2^59 */
  overflow2 <<= 1; /* overflow2 < 2^13 */

  out[0] += overflow1; /* out[0] < 2^60 */
  out[1] += overflow2; /* out[1] < 2^59 + 2^6 + 2^13 */

  out[1] += out[0] >> 58;
  out[0] &= bottom58bits;
  /* out[0] < 2^58
   * out[1] < 2^59 + 2^6 + 2^13 + 2^2
   *        < 2^59 + 2^14 */
}

static void
felem_square_reduce(felem out, const felem in)
{
  largefelem tmp;
  felem_square(tmp, in);
  felem_reduce(out, tmp);
}

static void
felem_mul_reduce(felem out, const felem in1, const felem in2)
{
  largefelem tmp;
  felem_mul(tmp, in1, in2);
  felem_reduce(out, tmp);
}

/* felem_inv calculates |out| = |in|^{-1}
 *
 * Based on Fermat's Little Theorem:
 *   a^p = a (mod p)
 *   a^{p-1} = 1 (mod p)
 *   a^{p-2} = a^{-1} (mod p)
 */
static void
felem_inv(felem out, const felem in)
{
  felem ftmp, ftmp2, ftmp3, ftmp4;
  largefelem tmp;
  unsigned i;

  felem_square(tmp, in);
  felem_reduce(ftmp, tmp); /* 2^1 */
  felem_mul(tmp, in, ftmp);
  felem_reduce(ftmp, tmp); /* 2^2 - 2^0 */
  felem_assign(ftmp2, ftmp);
  felem_square(tmp, ftmp);
  felem_reduce(ftmp, tmp); /* 2^3 - 2^1 */
  felem_mul(tmp, in, ftmp);
  felem_reduce(ftmp, tmp); /* 2^3 - 2^0 */
  felem_square(tmp, ftmp);
  felem_reduce(ftmp, tmp); /* 2^4 - 2^1 */

  felem_square(tmp, ftmp2);
  felem_reduce(ftmp3, tmp); /* 2^3 - 2^1 */
  felem_square(tmp, ftmp3);
  felem_reduce(ftmp3, tmp); /* 2^4 - 2^2 */
  felem_mul(tmp, ftmp3, ftmp2);
  felem_reduce(ftmp3, tmp); /* 2^4 - 2^0 */

  felem_assign(ftmp2, ftmp3);
  felem_square(tmp, ftmp3);
  felem_reduce(ftmp3, tmp); /* 2^5 - 2^1 */
  felem_square(tmp, ftmp3);
  felem_reduce(ftmp3, tmp); /* 2^6 - 2^2 */
  felem_square(tmp, ftmp3);
  felem_reduce(ftmp3, tmp); /* 2^7 - 2^3 */
  felem_square(tmp, ftmp3);
  felem_reduce(ftmp3, tmp); /* 2^8 - 2^4 */
  felem_assign(ftmp4, ftmp3);
  felem_mul(tmp, ftmp3, ftmp);
  felem_reduce(ftmp4, tmp); /* 2^8 - 2^1 */
  felem_square(tmp, ftmp4);
  felem_reduce(ftmp4, tmp); /* 2^9 - 2^2 */
  felem_mul(tmp, ftmp3, ftmp2);
  felem_reduce(ftmp3, tmp); /* 2^8 - 2^0 */
  felem_assign(ftmp2, ftmp3);

  for (i = 0; i < 8; i++) {
    felem_square(tmp, ftmp3);
    felem_reduce(ftmp3, tmp); /* 2^16 - 2^8 */
  }
  felem_mul(tmp, ftmp3, ftmp2);
  felem_reduce(ftmp3, tmp); /* 2^16 - 2^0 */
  felem_assign(ftmp2, ftmp3);

  for (i = 0; i < 16; i++) {
    felem_square(tmp, ftmp3);
    felem_reduce(ftmp3, tmp); /* 2^32 - 2^16 */
  }
  felem_mul(tmp, ftmp3, ftmp2);
  felem_reduce(ftmp3, tmp); /* 2^32 - 2^0 */
  felem_assign(ftmp2, ftmp3);

  for (i = 0; i < 32; i++) {
    felem_square(tmp, ftmp3);
    felem_reduce(ftmp3, tmp); /* 2^64 - 2^32 */
  }
  felem_mul(tmp, ftmp3, ftmp2);
  felem_reduce(ftmp3, tmp); /* 2^64 - 2^0 */
  felem_assign(ftmp2, ftmp3);

  for (i = 0; i < 64; i++) {
    felem_square(tmp, ftmp3);
    felem_reduce(ftmp3, tmp); /* 2^128 - 2^64 */
  }
  felem_mul(tmp, ftmp3, ftmp2);
  felem_reduce(ftmp3, tmp); /* 2^128 - 2^0 */
  felem_assign(ftmp2, ftmp3);

  for (i = 0; i < 128; i++) {
    felem_square(tmp, ftmp3);
    felem_reduce(ftmp3, tmp); /* 2^256 - 2^128 */
  }
  felem_mul(tmp, ftmp3, ftmp2);
  felem_reduce(ftmp3, tmp); /* 2^256 - 2^0 */
  felem_assign(ftmp2, ftmp3);

  for (i = 0; i < 256; i++) {
    felem_square(tmp, ftmp3);
    felem_reduce(ftmp3, tmp); /* 2^512 - 2^256 */
  }
  felem_mul(tmp, ftmp3, ftmp2);
  felem_reduce(ftmp3, tmp); /* 2^512 - 2^0 */

  for (i = 0; i < 9; i++) {
    felem_square(tmp, ftmp3);
    felem_reduce(ftmp3, tmp); /* 2^521 - 2^9 */
  }
  felem_mul(tmp, ftmp3, ftmp4);
  felem_reduce(ftmp3, tmp); /* 2^512 - 2^2 */
  felem_mul(tmp, ftmp3, in);
  felem_reduce(out, tmp); /* 2^512 - 3 */
}

/* This is 2^521-1, expressed as an felem */
static const felem kPrime = { 0x03ffffffffffffff, 0x03ffffffffffffff,
                              0x03ffffffffffffff, 0x03ffffffffffffff,
                              0x03ffffffffffffff, 0x03ffffffffffffff,
                              0x03ffffffffffffff, 0x03ffffffffffffff,
                              0x01ffffffffffffff };

/* felem_is_zero returns a limb with all bits set if |in| == 0 (mod p) and 0
 * otherwise.
 * On entry:
 *   in[i] < 2^59 + 2^14
 */
static limb
felem_is_zero(const felem in)
{
  felem ftmp;
  limb is_zero, is_p;
  felem_assign(ftmp, in);

  ftmp[0] += ftmp[8] >> 57;
  ftmp[8] &= bottom57bits;
  /* ftmp[8] < 2^57 */
  ftmp[1] += ftmp[0] >> 58;
  ftmp[0] &= bottom58bits;
  ftmp[2] += ftmp[1] >> 58;
  ftmp[1] &= bottom58bits;
  ftmp[3] += ftmp[2] >> 58;
  ftmp[2] &= bottom58bits;
  ftmp[4] += ftmp[3] >> 58;
  ftmp[3] &= bottom58bits;
  ftmp[5] += ftmp[4] >> 58;
  ftmp[4] &= bottom58bits;
  ftmp[6] += ftmp[5] >> 58;
  ftmp[5] &= bottom58bits;
  ftmp[7] += ftmp[6] >> 58;
  ftmp[6] &= bottom58bits;
  ftmp[8] += ftmp[7] >> 58;
  ftmp[7] &= bottom58bits;
  /* ftmp[8] < 2^57 + 4 */

  /* The ninth limb of 2*(2^521-1) is 0x03ffffffffffffff, which is
   * greater than our bound for ftmp[8]. Therefore we only have to check
   * if the zero is zero or 2^521-1. */

  is_zero = 0;
  is_zero |= ftmp[0];
  is_zero |= ftmp[1];
  is_zero |= ftmp[2];
  is_zero |= ftmp[3];
  is_zero |= ftmp[4];
  is_zero |= ftmp[5];
  is_zero |= ftmp[6];
  is_zero |= ftmp[7];
  is_zero |= ftmp[8];

  is_zero--;
  /* We know that ftmp[i] < 2^63, therefore the only way that the top bit
   * can be set is if is_zero was 0 before the decrement. */
  is_zero = ((s64)is_zero) >> 63;

  is_p = ftmp[0] ^ kPrime[0];
  is_p |= ftmp[1] ^ kPrime[1];
  is_p |= ftmp[2] ^ kPrime[2];
  is_p |= ftmp[3] ^ kPrime[3];
  is_p |= ftmp[4] ^ kPrime[4];
  is_p |= ftmp[5] ^ kPrime[5];
  is_p |= ftmp[6] ^ kPrime[6];
  is_p |= ftmp[7] ^ kPrime[7];
  is_p |= ftmp[8] ^ kPrime[8];

  is_p--;
  is_p = ((s64)is_p) >> 63;

  is_zero |= is_p;
  return is_zero;
}

static int
felem_is_zero_int(const felem in)
{
  return (int)(felem_is_zero(in) & ((limb)1));
}

/* felem_contract converts |in| to its unique, minimal representation.
 * On entry:
 *   in[i] < 2^59 + 2^14
 */
static void
felem_contract(felem out, const felem in)
{
  limb is_p, is_greater, sign;
  static const limb two58 = ((limb)1) << 58;

  felem_assign(out, in);

  out[0] += out[8] >> 57;
  out[8] &= bottom57bits;
  /* out[8] < 2^57 */
  out[1] += out[0] >> 58;
  out[0] &= bottom58bits;
  out[2] += out[1] >> 58;
  out[1] &= bottom58bits;
  out[3] += out[2] >> 58;
  out[2] &= bottom58bits;
  out[4] += out[3] >> 58;
  out[3] &= bottom58bits;
  out[5] += out[4] >> 58;
  out[4] &= bottom58bits;
  out[6] += out[5] >> 58;
  out[5] &= bottom58bits;
  out[7] += out[6] >> 58;
  out[6] &= bottom58bits;
  out[8] += out[7] >> 58;
  out[7] &= bottom58bits;
  /* out[8] < 2^57 + 4 */

  /* If the value is greater than 2^521-1 then we have to subtract
   * 2^521-1 out. See the comments in felem_is_zero regarding why we
   * don't test for other multiples of the prime. */

  /* First, if |out| is equal to 2^521-1, we subtract it out to get zero. */

  is_p = out[0] ^ kPrime[0];
  is_p |= out[1] ^ kPrime[1];
  is_p |= out[2] ^ kPrime[2];
  is_p |= out[3] ^ kPrime[3];
  is_p |= out[4] ^ kPrime[4];
  is_p |= out[5] ^ kPrime[5];
  is_p |= out[6] ^ kPrime[6];
  is_p |= out[7] ^ kPrime[7];
  is_p |= out[8] ^ kPrime[8];

  is_p--;
  is_p &= is_p << 32;
  is_p &= is_p << 16;
  is_p &= is_p << 8;
  is_p &= is_p << 4;
  is_p &= is_p << 2;
  is_p &= is_p << 1;
  is_p = ((s64)is_p) >> 63;
  is_p = ~is_p;

  /* is_p is 0 iff |out| == 2^521-1 and all ones otherwise */

  out[0] &= is_p;
  out[1] &= is_p;
  out[2] &= is_p;
  out[3] &= is_p;
  out[4] &= is_p;
  out[5] &= is_p;
  out[6] &= is_p;
  out[7] &= is_p;
  out[8] &= is_p;

  /* In order to test that |out| >= 2^521-1 we need only test if out[8]
   * >> 57 is greater than zero as (2^521-1) + x >= 2^522 */
  is_greater = out[8] >> 57;
  is_greater |= is_greater << 32;
  is_greater |= is_greater << 16;
  is_greater |= is_greater << 8;
  is_greater |= is_greater << 4;
  is_greater |= is_greater << 2;
  is_greater |= is_greater << 1;
  is_greater = ((s64)is_greater) >> 63;

  out[0] -= kPrime[0] & is_greater;
  out[1] -= kPrime[1] & is_greater;
  out[2] -= kPrime[2] & is_greater;
  out[3] -= kPrime[3] & is_greater;
  out[4] -= kPrime[4] & is_greater;
  out[5] -= kPrime[5] & is_greater;
  out[6] -= kPrime[6] & is_greater;
  out[7] -= kPrime[7] & is_greater;
  out[8] -= kPrime[8] & is_greater;

  /* Eliminate negative coefficients */
  sign = -(out[0] >> 63);
  out[0] += (two58 & sign);
  out[1] -= (1 & sign);
  sign = -(out[1] >> 63);
  out[1] += (two58 & sign);
  out[2] -= (1 & sign);
  sign = -(out[2] >> 63);
  out[2] += (two58 & sign);
  out[3] -= (1 & sign);
  sign = -(out[3] >> 63);
  out[3] += (two58 & sign);
  out[4] -= (1 & sign);
  sign = -(out[4] >> 63);
  out[4] += (two58 & sign);
  out[5] -= (1 & sign);
  sign = -(out[0] >> 63);
  out[5] += (two58 & sign);
  out[6] -= (1 & sign);
  sign = -(out[6] >> 63);
  out[6] += (two58 & sign);
  out[7] -= (1 & sign);
  sign = -(out[7] >> 63);
  out[7] += (two58 & sign);
  out[8] -= (1 & sign);
  sign = -(out[5] >> 63);
  out[5] += (two58 & sign);
  out[6] -= (1 & sign);
  sign = -(out[6] >> 63);
  out[6] += (two58 & sign);
  out[7] -= (1 & sign);
  sign = -(out[7] >> 63);
  out[7] += (two58 & sign);
  out[8] -= (1 & sign);
}

/* Group operations
 * ----------------
 *
 * Building on top of the field operations we have the operations on the
 * elliptic curve group itself. Points on the curve are represented in Jacobian
 * coordinates */

/* point_double calcuates 2*(x_in, y_in, z_in)
 *
 * The method is taken from:
 *   http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-3.html#doubling-dbl-2001-b
 *
 * Outputs can equal corresponding inputs, i.e., x_out == x_in is allowed.
 * while x_out == y_in is not (maybe this works, but it's not tested). */
static void
point_double(felem x_out, felem y_out, felem z_out, const felem x_in,
             const felem y_in, const felem z_in)
{
  largefelem tmp, tmp2;
  felem delta, gamma, beta, alpha, ftmp, ftmp2;

  felem_assign(ftmp, x_in);
  felem_assign(ftmp2, x_in);

  /* delta = z^2 */
  felem_square(tmp, z_in);
  felem_reduce(delta, tmp); /* delta[i] < 2^59 + 2^14 */

  /* gamma = y^2 */
  felem_square(tmp, y_in);
  felem_reduce(gamma, tmp); /* gamma[i] < 2^59 + 2^14 */

  /* beta = x*gamma */
  felem_mul(tmp, x_in, gamma);
  felem_reduce(beta, tmp); /* beta[i] < 2^59 + 2^14 */

  /* alpha = 3*(x-delta)*(x+delta) */
  felem_diff64(ftmp, delta);
  /* ftmp[i] < 2^61 */
  felem_sum64(ftmp2, delta);
  /* ftmp2[i] < 2^60 + 2^15 */
  felem_scalar64(ftmp2, 3);
  /* ftmp2[i] < 3*2^60 + 3*2^15 */
  felem_mul(tmp, ftmp, ftmp2);
  /* tmp[i] < 17(3*2^121 + 3*2^76)
   *        = 61*2^121 + 61*2^76
   *        < 64*2^121 + 64*2^76
   *        = 2^127 + 2^82
   *        < 2^128 */
  felem_reduce(alpha, tmp);

  /* x' = alpha^2 - 8*beta */
  felem_square(tmp, alpha);
  /* tmp[i] < 17*2^120
   *        < 2^125 */
  felem_assign(ftmp, beta);
  felem_scalar64(ftmp, 8);
  /* ftmp[i] < 2^62 + 2^17 */
  felem_diff_128_64(tmp, ftmp);
  /* tmp[i] < 2^125 + 2^63 + 2^62 + 2^17 */
  felem_reduce(x_out, tmp);

  /* z' = (y + z)^2 - gamma - delta */
  felem_sum64(delta, gamma);
  /* delta[i] < 2^60 + 2^15 */
  felem_assign(ftmp, y_in);
  felem_sum64(ftmp, z_in);
  /* ftmp[i] < 2^60 + 2^15 */
  felem_square(tmp, ftmp);
  /* tmp[i] < 17(2^122)
   *        < 2^127 */
  felem_diff_128_64(tmp, delta);
  /* tmp[i] < 2^127 + 2^63 */
  felem_reduce(z_out, tmp);

  /* y' = alpha*(4*beta - x') - 8*gamma^2 */
  felem_scalar64(beta, 4);
  /* beta[i] < 2^61 + 2^16 */
  felem_diff64(beta, x_out);
  /* beta[i] < 2^61 + 2^60 + 2^16 */
  felem_mul(tmp, alpha, beta);
  /* tmp[i] < 17*((2^59 + 2^14)(2^61 + 2^60 + 2^16))
   *        = 17*(2^120 + 2^75 + 2^119 + 2^74 + 2^75 + 2^30)
   *        = 17*(2^120 + 2^119 + 2^76 + 2^74 + 2^30)
   *        < 2^128 */
  felem_square(tmp2, gamma);
  /* tmp2[i] < 17*(2^59 + 2^14)^2
   *         = 17*(2^118 + 2^74 + 2^28) */
  felem_scalar128(tmp2, 8);
  /* tmp2[i] < 8*17*(2^118 + 2^74 + 2^28)
   *         = 2^125 + 2^121 + 2^81 + 2^77 + 2^35 + 2^31
   *         < 2^126 */
  felem_diff128(tmp, tmp2);
  /* tmp[i] < 2^127 - 2^69 + 17(2^120 + 2^119 + 2^76 + 2^74 + 2^30)
   *        = 2^127 + 2^124 + 2^122 + 2^120 + 2^118 + 2^80 + 2^78 + 2^76 +
   *          2^74 + 2^69 + 2^34 + 2^30
   *        < 2^128 */
  felem_reduce(y_out, tmp);
}

/* copy_conditional copies in to out iff mask is all ones. */
static void
copy_conditional(felem out, const felem in, limb mask)
{
  unsigned i;
  for (i = 0; i < NLIMBS; ++i) {
    const limb tmp = mask & (in[i] ^ out[i]);
    out[i] ^= tmp;
  }
}

/* point_add calcuates (x1, y1, z1) + (x2, y2, z2)
 *
 * The method is taken from
 *   http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-3.html#addition-add-2007-bl,
 * adapted for mixed addition (z2 = 1, or z2 = 0 for the point at infinity).
 *
 * This function includes a branch for checking whether the two input points
 * are equal (while not equal to the point at infinity). This case never
 * happens during single point multiplication, so there is no timing leak for
 * ECDH or ECDSA signing. */
static void
point_add(felem x3, felem y3, felem z3, const felem x1, const felem y1,
          const felem z1, const int mixed, const felem x2, const felem y2,
          const felem z2)
{
  felem ftmp, ftmp2, ftmp3, ftmp4, ftmp5, ftmp6, x_out, y_out, z_out;
  largefelem tmp, tmp2;
  limb x_equal, y_equal, z1_is_zero, z2_is_zero;

  z1_is_zero = felem_is_zero(z1);
  z2_is_zero = felem_is_zero(z2);

  /* ftmp = z1z1 = z1**2 */
  felem_square(tmp, z1);
  felem_reduce(ftmp, tmp);

  if (!mixed) {
    /* ftmp2 = z2z2 = z2**2 */
    felem_square(tmp, z2);
    felem_reduce(ftmp2, tmp);

    /* u1 = ftmp3 = x1*z2z2 */
    felem_mul(tmp, x1, ftmp2);
    felem_reduce(ftmp3, tmp);

    /* ftmp5 = z1 + z2 */
    felem_assign(ftmp5, z1);
    felem_sum64(ftmp5, z2);
    /* ftmp5[i] < 2^61 */

    /* ftmp5 = (z1 + z2)**2 - z1z1 - z2z2 = 2*z1z2 */
    felem_square(tmp, ftmp5);
    /* tmp[i] < 17*2^122 */
    felem_diff_128_64(tmp, ftmp);
    /* tmp[i] < 17*2^122 + 2^63 */
    felem_diff_128_64(tmp, ftmp2);
    /* tmp[i] < 17*2^122 + 2^64 */
    felem_reduce(ftmp5, tmp);

    /* ftmp2 = z2 * z2z2 */
    felem_mul(tmp, ftmp2, z2);
    felem_reduce(ftmp2, tmp);

    /* s1 = ftmp6 = y1 * z2**3 */
    felem_mul(tmp, y1, ftmp2);
    felem_reduce(ftmp6, tmp);
  } else {
    /* We'll assume z2 = 1 (special case z2 = 0 is handled later) */

    /* u1 = ftmp3 = x1*z2z2 */
    felem_assign(ftmp3, x1);

    /* ftmp5 = 2*z1z2 */
    felem_scalar(ftmp5, z1, 2);

    /* s1 = ftmp6 = y1 * z2**3 */
    felem_assign(ftmp6, y1);
  }

  /* u2 = x2*z1z1 */
  felem_mul(tmp, x2, ftmp);
  /* tmp[i] < 17*2^120 */

  /* h = ftmp4 = u2 - u1 */
  felem_diff_128_64(tmp, ftmp3);
  /* tmp[i] < 17*2^120 + 2^63 */
  felem_reduce(ftmp4, tmp);

  x_equal = felem_is_zero(ftmp4);

  /* z_out = ftmp5 * h */
  felem_mul(tmp, ftmp5, ftmp4);
  felem_reduce(z_out, tmp);

  /* ftmp = z1 * z1z1 */
  felem_mul(tmp, ftmp, z1);
  felem_reduce(ftmp, tmp);

  /* s2 = tmp = y2 * z1**3 */
  felem_mul(tmp, y2, ftmp);
  /* tmp[i] < 17*2^120 */

  /* r = ftmp5 = (s2 - s1)*2 */
  felem_diff_128_64(tmp, ftmp6);
  /* tmp[i] < 17*2^120 + 2^63 */
  felem_reduce(ftmp5, tmp);
  y_equal = felem_is_zero(ftmp5);
  felem_scalar64(ftmp5, 2);
  /* ftmp5[i] < 2^61 */

  if (x_equal && y_equal && !z1_is_zero && !z2_is_zero) {
    point_double(x3, y3, z3, x1, y1, z1);
    return;
  }

  /* I = ftmp = (2h)**2 */
  felem_assign(ftmp, ftmp4);
  felem_scalar64(ftmp, 2);
  /* ftmp[i] < 2^61 */
  felem_square(tmp, ftmp);
  /* tmp[i] < 17*2^122 */
  felem_reduce(ftmp, tmp);

  /* J = ftmp2 = h * I */
  felem_mul(tmp, ftmp4, ftmp);
  felem_reduce(ftmp2, tmp);

  /* V = ftmp4 = U1 * I */
  felem_mul(tmp, ftmp3, ftmp);
  felem_reduce(ftmp4, tmp);

  /* x_out = r**2 - J - 2V */
  felem_square(tmp, ftmp5);
  /* tmp[i] < 17*2^122 */
  felem_diff_128_64(tmp, ftmp2);
  /* tmp[i] < 17*2^122 + 2^63 */
  felem_assign(ftmp3, ftmp4);
  felem_scalar64(ftmp4, 2);
  /* ftmp4[i] < 2^61 */
  felem_diff_128_64(tmp, ftmp4);
  /* tmp[i] < 17*2^122 + 2^64 */
  felem_reduce(x_out, tmp);

  /* y_out = r(V-x_out) - 2 * s1 * J */
  felem_diff64(ftmp3, x_out);
  /* ftmp3[i] < 2^60 + 2^60
   *          = 2^61 */
  felem_mul(tmp, ftmp5, ftmp3);
  /* tmp[i] < 17*2^122 */
  felem_mul(tmp2, ftmp6, ftmp2);
  /* tmp2[i] < 17*2^120 */
  felem_scalar128(tmp2, 2);
  /* tmp2[i] < 17*2^121 */
  felem_diff128(tmp, tmp2);
  /* tmp[i] < 2^127 - 2^69 + 17*2^122
   *        = 2^126 - 2^122 - 2^6 - 2^2 - 1
   *        < 2^127 */
  felem_reduce(y_out, tmp);

  copy_conditional(x_out, x2, z1_is_zero);
  copy_conditional(x_out, x1, z2_is_zero);
  copy_conditional(y_out, y2, z1_is_zero);
  copy_conditional(y_out, y1, z2_is_zero);
  copy_conditional(z_out, z2, z1_is_zero);
  copy_conditional(z_out, z1, z2_is_zero);
  felem_assign(x3, x_out);
  felem_assign(y3, y_out);
  felem_assign(z3, z_out);
}

/* Base point pre computation
 * --------------------------
 *
 * Two different sorts of precomputed tables are used in the following code.
 * Each contain various points on the curve, where each point is three field
 * elements (x, y, z).
 *
 * For the base point table, z is usually 1 (0 for the point at infinity).
 * This table has 16 elements:
 * index | bits    | point
 * ------+---------+------------------------------
 *     0 | 0 0 0 0 | 0G
 *     1 | 0 0 0 1 | 1G
 *     2 | 0 0 1 0 | 2^130G
 *     3 | 0 0 1 1 | (2^130 + 1)G
 *     4 | 0 1 0 0 | 2^260G
 *     5 | 0 1 0 1 | (2^260 + 1)G
 *     6 | 0 1 1 0 | (2^260 + 2^130)G
 *     7 | 0 1 1 1 | (2^260 + 2^130 + 1)G
 *     8 | 1 0 0 0 | 2^390G
 *     9 | 1 0 0 1 | (2^390 + 1)G
 *    10 | 1 0 1 0 | (2^390 + 2^130)G
 *    11 | 1 0 1 1 | (2^390 + 2^130 + 1)G
 *    12 | 1 1 0 0 | (2^390 + 2^260)G
 *    13 | 1 1 0 1 | (2^390 + 2^260 + 1)G
 *    14 | 1 1 1 0 | (2^390 + 2^260 + 2^130)G
 *    15 | 1 1 1 1 | (2^390 + 2^260 + 2^130 + 1)G
 *
 * The reason for this is so that we can clock bits into four different
 * locations when doing simple scalar multiplies against the base point.
 *
 * Tables for other points have table[i] = iG for i in 0 .. 16. */

/* gmul is the table of precomputed base points */
static const felem gmul[16][3] = {
  { { 0, 0, 0, 0, 0, 0, 0, 0, 0 },
    { 0, 0, 0, 0, 0, 0, 0, 0, 0 },
    { 0, 0, 0, 0, 0, 0, 0, 0, 0 } },
  { { 0x017e7e31c2e5bd66, 0x022cf0615a90a6fe, 0x00127a2ffa8de334,
      0x01dfbf9d64a3f877, 0x006b4d3dbaa14b5e, 0x014fed487e0a2bd8,
      0x015b4429c6481390, 0x03a73678fb2d988e, 0x00c6858e06b70404 },
    { 0x00be94769fd16650, 0x031c21a89cb09022, 0x039013fad0761353,
      0x02657bd099031542, 0x03273e662c97ee72, 0x01e6d11a05ebef45,
      0x03d1bd998f544495, 0x03001172297ed0b1, 0x011839296a789a3b },
    { 1, 0, 0, 0, 0, 0, 0, 0, 0 } },
  { { 0x0373faacbc875bae, 0x00f325023721c671, 0x00f666fd3dbde5ad,
      0x01a6932363f88ea7, 0x01fc6d9e13f9c47b, 0x03bcbffc2bbf734e,
      0x013ee3c3647f3a92, 0x029409fefe75d07d, 0x00ef9199963d85e5 },
    { 0x011173743ad5b178, 0x02499c7c21bf7d46, 0x035beaeabb8b1a58,
      0x00f989c4752ea0a3, 0x0101e1de48a9c1a3, 0x01a20076be28ba6c,
      0x02f8052e5eb2de95, 0x01bfe8f82dea117c, 0x0160074d3c36ddb7 },
    { 1, 0, 0, 0, 0, 0, 0, 0, 0 } },
  { { 0x012f3fc373393b3b, 0x03d3d6172f1419fa, 0x02adc943c0b86873,
      0x00d475584177952b, 0x012a4d1673750ee2, 0x00512517a0f13b0c,
      0x02b184671a7b1734, 0x0315b84236f1a50a, 0x00a4afc472edbdb9 },
    { 0x00152a7077f385c4, 0x03044007d8d1c2ee, 0x0065829d61d52b52,
      0x00494ff6b6631d0d, 0x00a11d94d5f06bcf, 0x02d2f89474d9282e,
      0x0241c5727c06eeb9, 0x0386928710fbdb9d, 0x01f883f727b0dfbe },
    { 1, 0, 0, 0, 0, 0, 0, 0, 0 } },
  { { 0x019b0c3c9185544d, 0x006243a37c9d97db, 0x02ee3cbe030a2ad2,
      0x00cfdd946bb51e0d, 0x0271c00932606b91, 0x03f817d1ec68c561,
      0x03f37009806a369c, 0x03c1f30baf184fd5, 0x01091022d6d2f065 },
    { 0x0292c583514c45ed, 0x0316fca51f9a286c, 0x00300af507c1489a,
      0x0295f69008298cf1, 0x02c0ed8274943d7b, 0x016509b9b47a431e,
      0x02bc9de9634868ce, 0x005b34929bffcb09, 0x000c1a0121681524 },
    { 1, 0, 0, 0, 0, 0, 0, 0, 0 } },
  { { 0x0286abc0292fb9f2, 0x02665eee9805b3f7, 0x01ed7455f17f26d6,
      0x0346355b83175d13, 0x006284944cd0a097, 0x0191895bcdec5e51,
      0x02e288370afda7d9, 0x03b22312bfefa67a, 0x01d104d3fc0613fe },
    { 0x0092421a12f7e47f, 0x0077a83fa373c501, 0x03bd25c5f696bd0d,
      0x035c41e4d5459761, 0x01ca0d1742b24f53, 0x00aaab27863a509c,
      0x018b6de47df73917, 0x025c0b771705cd01, 0x01fd51d566d760a7 },
    { 1, 0, 0, 0, 0, 0, 0, 0, 0 } },
  { { 0x01dd92ff6b0d1dbd, 0x039c5e2e8f8afa69, 0x0261ed13242c3b27,
      0x0382c6e67026e6a0, 0x01d60b10be2089f9, 0x03c15f3dce86723f,
      0x03c764a32d2a062d, 0x017307eac0fad056, 0x018207c0b96c5256 },
    { 0x0196a16d60e13154, 0x03e6ce74c0267030, 0x00ddbf2b4e52a5aa,
      0x012738241bbf31c8, 0x00ebe8dc04685a28, 0x024c2ad6d380d4a2,
      0x035ee062a6e62d0e, 0x0029ed74af7d3a0f, 0x00eef32aec142ebd },
    { 1, 0, 0, 0, 0, 0, 0, 0, 0 } },
  { { 0x00c31ec398993b39, 0x03a9f45bcda68253, 0x00ac733c24c70890,
      0x00872b111401ff01, 0x01d178c23195eafb, 0x03bca2c816b87f74,
      0x0261a9af46fbad7a, 0x0324b2a8dd3d28f9, 0x00918121d8f24e23 },
    { 0x032bc8c1ca983cd7, 0x00d869dfb08fc8c6, 0x01693cb61fce1516,
      0x012a5ea68f4e88a8, 0x010869cab88d7ae3, 0x009081ad277ceee1,
      0x033a77166d064cdc, 0x03955235a1fb3a95, 0x01251a4a9b25b65e },
    { 1, 0, 0, 0, 0, 0, 0, 0, 0 } },
  { { 0x00148a3a1b27f40b, 0x0123186df1b31fdc, 0x00026e7beaad34ce,
      0x01db446ac1d3dbba, 0x0299c1a33437eaec, 0x024540610183cbb7,
      0x0173bb0e9ce92e46, 0x02b937e43921214b, 0x01ab0436a9bf01b5 },
    { 0x0383381640d46948, 0x008dacbf0e7f330f, 0x03602122bcc3f318,
      0x01ee596b200620d6, 0x03bd0585fda430b3, 0x014aed77fd123a83,
      0x005ace749e52f742, 0x0390fe041da2b842, 0x0189a8ceb3299242 },
    { 1, 0, 0, 0, 0, 0, 0, 0, 0 } },
  { { 0x012a19d6b3282473, 0x00c0915918b423ce, 0x023a954eb94405ae,
      0x00529f692be26158, 0x0289fa1b6fa4b2aa, 0x0198ae4ceea346ef,
      0x0047d8cdfbdedd49, 0x00cc8c8953f0f6b8, 0x001424abbff49203 },
    { 0x0256732a1115a03a, 0x0351bc38665c6733, 0x03f7b950fb4a6447,
      0x000afffa94c22155, 0x025763d0a4dab540, 0x000511e92d4fc283,
      0x030a7e9eda0ee96c, 0x004c3cd93a28bf0a, 0x017edb3a8719217f },
    { 1, 0, 0, 0, 0, 0, 0, 0, 0 } },
  { { 0x011de5675a88e673, 0x031d7d0f5e567fbe, 0x0016b2062c970ae5,
      0x03f4a2be49d90aa7, 0x03cef0bd13822866, 0x03f0923dcf774a6c,
      0x0284bebc4f322f72, 0x016ab2645302bb2c, 0x01793f95dace0e2a },
    { 0x010646e13527a28f, 0x01ca1babd59dc5e7, 0x01afedfd9a5595df,
      0x01f15785212ea6b1, 0x0324e5d64f6ae3f4, 0x02d680f526d00645,
      0x0127920fadf627a7, 0x03b383f75df4f684, 0x0089e0057e783b0a },
    { 1, 0, 0, 0, 0, 0, 0, 0, 0 } },
  { { 0x00f334b9eb3c26c6, 0x0298fdaa98568dce, 0x01c2d24843a82292,
      0x020bcb24fa1b0711, 0x02cbdb3d2b1875e6, 0x0014907598f89422,
      0x03abe3aa43b26664, 0x02cbf47f720bc168, 0x0133b5e73014b79b },
    { 0x034aab5dab05779d, 0x00cdc5d71fee9abb, 0x0399f16bd4bd9d30,
      0x03582fa592d82647, 0x02be1cdfb775b0e9, 0x0034f7cea32e94cb,
      0x0335a7f08f56f286, 0x03b707e9565d1c8b, 0x0015c946ea5b614f },
    { 1, 0, 0, 0, 0, 0, 0, 0, 0 } },
  { { 0x024676f6cff72255, 0x00d14625cac96378, 0x00532b6008bc3767,
      0x01fc16721b985322, 0x023355ea1b091668, 0x029de7afdc0317c3,
      0x02fc8a7ca2da037c, 0x02de1217d74a6f30, 0x013f7173175b73bf },
    { 0x0344913f441490b5, 0x0200f9e272b61eca, 0x0258a246b1dd55d2,
      0x03753db9ea496f36, 0x025e02937a09c5ef, 0x030cbd3d14012692,
      0x01793a67e70dc72a, 0x03ec1d37048a662e, 0x006550f700c32a8d },
    { 1, 0, 0, 0, 0, 0, 0, 0, 0 } },
  { { 0x00d3f48a347eba27, 0x008e636649b61bd8, 0x00d3b93716778fb3,
      0x004d1915757bd209, 0x019d5311a3da44e0, 0x016d1afcbbe6aade,
      0x0241bf5f73265616, 0x0384672e5d50d39b, 0x005009fee522b684 },
    { 0x029b4fab064435fe, 0x018868ee095bbb07, 0x01ea3d6936cc92b8,
      0x000608b00f78a2f3, 0x02db911073d1c20f, 0x018205938470100a,
      0x01f1e4964cbe6ff2, 0x021a19a29eed4663, 0x01414485f42afa81 },
    { 1, 0, 0, 0, 0, 0, 0, 0, 0 } },
  { { 0x01612b3a17f63e34, 0x03813992885428e6, 0x022b3c215b5a9608,
      0x029b4057e19f2fcb, 0x0384059a587af7e6, 0x02d6400ace6fe610,
      0x029354d896e8e331, 0x00c047ee6dfba65e, 0x0037720542e9d49d },
    { 0x02ce9eed7c5e9278, 0x0374ed703e79643b, 0x01316c54c4072006,
      0x005aaa09054b2ee8, 0x002824000c840d57, 0x03d4eba24771ed86,
      0x0189c50aabc3bdae, 0x0338c01541e15510, 0x00466d56e38eed42 },
    { 1, 0, 0, 0, 0, 0, 0, 0, 0 } },
  { { 0x007efd8330ad8bd6, 0x02465ed48047710b, 0x0034c6606b215e0c,
      0x016ae30c53cbf839, 0x01fa17bd37161216, 0x018ead4e61ce8ab9,
      0x005482ed5f5dee46, 0x037543755bba1d7f, 0x005e5ac7e70a9d0f },
    { 0x0117e1bb2fdcb2a2, 0x03deea36249f40c4, 0x028d09b4a6246cb7,
      0x03524b8855bcf756, 0x023d7d109d5ceb58, 0x0178e43e3223ef9c,
      0x0154536a0c6e966a, 0x037964d1286ee9fe, 0x0199bcd90e125055 },
    { 1, 0, 0, 0, 0, 0, 0, 0, 0 } }
};

/* select_point selects the |idx|th point from a precomputation table and
 * copies it to out. */
static void
select_point(const limb idx, unsigned int size,
             const felem pre_comp[/* size */][3], felem out[3])
{
  unsigned i, j;
  limb* outlimbs = &out[0][0];
  memset(outlimbs, 0, 3 * sizeof(felem));

  for (i = 0; i < size; i++) {
    const limb* inlimbs = &pre_comp[i][0][0];
    limb mask = i ^ idx;
    mask |= mask >> 4;
    mask |= mask >> 2;
    mask |= mask >> 1;
    mask &= 1;
    mask--;
    for (j = 0; j < NLIMBS * 3; j++)
      outlimbs[j] |= inlimbs[j] & mask;
  }
}

/* get_bit returns the |i|th bit in |in| */
static char
get_bit(const felem_bytearray in, int i)
{
  if (i < 0)
    return 0;
  return (in[i >> 3] >> (i & 7)) & 1;
}

/* Now to implement our desired functions */
static void to_affine(felem x2, felem y2, const felem x1, const felem y1, const felem z1){
  felem zinv;
  felem zinvsqr;
  felem zinvcube;
  felem_inv(zinv, z1);
  felem_square_reduce(zinvsqr, zinv);
  felem_mul_reduce(zinvcube, zinv, zinvsqr);
  felem_mul_reduce(x2, x1, zinvsqr);
  felem_mul_reduce(y2, y1, zinvcube);
}

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

static limb condmask(int cond){
  limb ret = 1-cond; //0 or 1
  ret--;
  return ret;
}
  
static void scalarmult(felem x2, felem y2, const unsigned char scalar[66], const felem x1, const felem y1){
  felem z2 = {0};
  felem tmp[3];
  felem negY;
  felem table[17][3];
  int scalar_s[105];
  int scalar_d[105];
  int must_double=0;
  int i;
  memset(table, 0, sizeof(table));
  felem_one(x2);
  felem_one(y2);
  felem_one(negY);
  felem_one(table[0][0]);
  felem_one(table[0][1]);
  felem_assign(table[1][0], x1);
  felem_assign(table[1][1], y1);
  felem_one(table[1][2]);
  recode(scalar_d, scalar_s, scalar);
  for(int i=0; i<17; i++){
    if(i%2==0){
      point_double(table[i][0], table[i][1], table[i][2], table[i/2][0], table[i/2][1], table[i/2][2]);
    }else {
      point_add(table[i][0], table[i][1], table[i][2], table[i-1][0], table[i-1][1], table[i-1][2], 1,
             x1, y1, negY);
    }
  }
  for(i=104; i>=0; i--){
    if (must_double) {
      point_double(x2, y2, z2, x2, y2, z2);
      point_double(x2, y2, z2, x2, y2, z2);
      point_double(x2, y2, z2, x2, y2, z2);
      point_double(x2, y2, z2, x2, y2, z2);
      point_double(x2, y2, z2, x2, y2, z2);
    }
    must_double = 1;
    select_point(scalar_d[i], 17, table, tmp);
    felem_neg(negY, tmp[1]);
    copy_conditional(tmp[1], negY, condmask(scalar_s[i]));
    point_add(x2, y2, z2, x2, y2, z2, 0, tmp[0], tmp[1], tmp[2]);
  }
  to_affine(x2, y2, x2, y2, z2);
}

static void scalarmult_double(felem x3, felem y3, const unsigned char s1[66], const felem x1, const felem y1, const unsigned char s2[66], const felem x2, const felem y2){
  felem z3 = {0};
  felem tmp[3];
  felem table1[2][3];
  felem table2[2][3];
  limb idx;
  felem_one(x3);
  felem_one(y3);
  memset(table1, 0, sizeof(table1));
  memset(table2, 0, sizeof(table2));
  felem_one(table1[0][0]);
  felem_one(table1[0][1]);
  felem_assign(table1[1][0], x1);
  felem_assign(table1[1][1], y1);
  felem_one(table1[1][2]);
  felem_one(table2[0][0]);
  felem_one(table2[0][1]);
  felem_assign(table2[1][0], x2);
  felem_assign(table2[1][1], y2);
  felem_one(table2[1][2]);
  for(int i=520; i>=0; i--){
    idx = get_bit(s1, i);
    point_double(x3, y3, z3, x3, y3, z3);
    select_point(idx, 2, table1, tmp);
    point_add(x3, y3, z3, x3, y3, z3, 1, tmp[0], tmp[1], tmp[2]);
    idx = get_bit(s2, i);
    select_point(idx, 2, table2, tmp);
    point_add(x3, y3, z3, x3, y3, z3, 1, tmp[0], tmp[1], tmp[2]);
  }
  to_affine(x3, y3, x3, y3, z3);
}
static void load_coord(felem val, const u8 in[66]){
  u8 tmp[66];
  flip_endian(tmp, in, 66);
  bin66_to_felem(val, tmp);
}

static void dump_coord(u8 out[66], const felem v){
  u8 tmp[66];
  felem val;
  felem_contract(val, v);
  felem_to_bin66(tmp, val);
  flip_endian(out, tmp, 66);
}

void
p521_64_scalarmult(unsigned char q[132], const unsigned char scalar[66], const unsigned char p[132]){
  felem xin, yin, xout, yout;
  load_coord(xin, p);
  load_coord(yin, p+66);
  scalarmult(xout, yout, scalar, xin, yin);
  dump_coord(q, xout);
  dump_coord(q+66, yout);
}

void
p521_64_scalarmult_base(unsigned char q[132], const unsigned char scalar[66]){
  felem xin, yin, xout, yout;
  load_coord(xin, nistp521_curve_params[3]);
  load_coord(yin, nistp521_curve_params[4]);
  scalarmult(xout, yout, scalar, xin, yin);
  dump_coord(q, xout);
  dump_coord(q+66, yout);
}

void
p521_64_double_scalarmult_base(unsigned char q[132], const unsigned char a[132],
                                    const unsigned char n1[66],
                                    const unsigned char n2[66]){
  
  felem x1, y1, x2, y2, xout, yout;
  load_coord(x1, nistp521_curve_params[3]);
  load_coord(y1, nistp521_curve_params[4]);
  load_coord(x2, a);
  load_coord(y2, a+66);
  scalarmult_double(xout, yout, n1, x1, y1, n2, x2, y2);
  dump_coord(q, xout);
  dump_coord(q+66, yout);
}
