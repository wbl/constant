/* Use saturated 64 bit arithmetic and Montgomery reduction. */
#include<assert.h>
#include<stdint.h>
#include<inttypes.h>
#include<stdbool.h>
#include<stdio.h>
#include "p384_64.h"
/* Constants */
typedef uint64_t felem[6];
typedef __uint128_t uint128_t;

static const felem Rsqr = {0xfffffffe00000001,
                           0x200000000,
                           0xfffffffe00000000,
                           0x200000000,
                           0x1,
                           0x0};
static const felem R = {0xffffffff00000001,
                        0xffffffff,
                        0x1,
                        0x0,
                        0x0,
                        0x0};

static const felem prime = {0xffffffff,
                            0xffffffff00000000,
                            0xfffffffffffffffe,
                            0xffffffffffffffff,
                            0xffffffffffffffff,
                            0xffffffffffffffff};

static const felem curve_b = {0x2a85c8edd3ec2aef,
                              0xc656398d8a2ed19d,
                              0x314088f5013875a,
                              0x181d9c6efe814112,
                              0x988e056be3f82d19,
                              0xb3312fa7e23ee7e4};

static const felem base_x = {0x3a545e3872760ab7,
                             0x5502f25dbf55296c,
                             0x59f741e082542a38,
                             0x6e1d3b628ba79b98,
                             0x8eb1c71ef320ad74,
                             0xaa87ca22be8b0537};

static const felem base_y = {0x7a431d7c90ea0e5f,
                             0xa60b1ce1d7e819d,
                             0xe9da3113b5f0b8c0,
                             0xf8f41dbd289a147c,
                             0x5d9e98bf9292dc29,
                             0x3617de4a96262c6f};
static const uint64_t mont_const = 4294967297;
/* Debugging help */
static void
dumpelem(char *name, const felem b){
  return;
  printf("%s = 0 ", name);
  for(int i=0; i<6; i++){
    printf("+ (2**(64*%d))*%llu", i, b[i]);
  }
  printf("\n");
}

static void
dumprod(char *name, const uint64_t p[13]){
  return;
  printf("%s = 0 ", name);
  for(int i=0; i<13; i++){
    printf("+ (2**(64*%d))*%llu", i, p[i]);
  }
  printf("\n");
}

/* Representation dependent arithmetic */
static void reduce_add_sub(felem a, uint64_t carry){
  assert((carry==0) || (carry==1));
  uint64_t pb = 0;
  uint64_t b = 0;
  felem d;
  uint64_t do_sub;
  uint64_t mask_sub;
  uint64_t mask_nosub;
  for(int i=0; i<6; i++){
    b = 0;
    d[i] = a[i]-prime[i];
    b += (d[i]>a[i]);
    d[i] -= pb;
    b += (d[i] == UINT64_MAX) & pb;
    pb = b;
    assert((pb==0) || (pb==1));
  }
  do_sub = 1- ((carry + pb) & 0x1);
  mask_sub = 1+~do_sub;
  mask_nosub = ~mask_sub;
  for(int i=0; i<6; i++){
    a[i] = (d[i] & mask_sub) | (a[i] & mask_nosub);
  }
}

static void
add(felem r, const felem a, const felem b)
{
  uint64_t carryin = 0;
  uint64_t carryout = 0;
  uint64_t t;
  for(int i=0; i<6; i++){
    carryin = carryout;
    t = a[i] + b[i];
    carryout = t<a[i];
    t += carryin;
    carryout += (t == 0) & carryin;
    r[i] = t;
  }
  reduce_add_sub(r, carryout);
}

static void
negate(felem r, const felem a)
{
  uint64_t pb = 0;
  uint64_t b = 0;
  for(int i=0; i<6; i++){
    b = 0;
    r[i] = prime[i]-a[i];
    b += (r[i]>prime[i]);
    r[i] -= pb;
    b += (r[i] == UINT64_MAX) & pb;
    pb = b;
  }
  assert(pb==0);
  reduce_add_sub(r, 0);
}

static void
sub(felem r, const felem a, const felem b)
{
  felem tmp;
  negate(tmp, b);
  add(r, a, tmp);
}

static void
mult_nored(uint64_t prod[12], const felem a, const felem b){
  uint128_t t;
  uint64_t carry;
  for(int i=0; i<12; i++){
    prod[i] = 0;
  }
  for(int i=0; i<6; i++){
    carry = 0;
    for(int j=0; j<6; j++){
      t = ((uint128_t)a[i])*b[j]+prod[i+j]+carry;
      prod[i+j] = (uint64_t) t;
      carry = (uint64_t) (t>>64);
    }
    prod[6+i] = carry;
  }
}

static void
mult_red(felem r, uint64_t p[12]){
  // products are 1 bigger to hold carry from Montgomery reduction.
  uint128_t t;
  uint64_t carry;
  uint64_t delayed[6];
  uint64_t m;
  for (int i = 0; i < 6; i++) {
    m = p[i]*mont_const;
    carry = 0;
    for (int j = 0; j < 6; j++) { /* This adds a multiple of prime that makes p[i] zero */
      t = (uint128_t)p[i + j] + ((uint128_t)m) * prime[j] + carry;
      p[i + j] = (uint64_t)t;
      carry = (uint64_t)(t >> 64);
    }
    assert(p[i]==0);
    delayed[i] = carry;
  }
  carry = 0;
  for (int i = 0; i < 6; i++) {
    t = ((uint128_t)p[i + 6]) + carry + delayed[i];
    r[i] = (uint64_t) t;
    carry = (uint64_t) (t >> 64);
  }
  reduce_add_sub(r, carry);
}

static void
mult(felem r, const felem a, const felem b){
  uint64_t p[12];
  mult_nored(p, a, b);
  mult_red(r, p);
}

static void
sqr(felem r, const felem a){
  mult(r, a, a);
}

static bool
iszero(const felem r){
  uint64_t diff = 0;
  for(int i=0; i<6; i++){
    diff |= r[i];
  }
  return diff == 0;
}

static void
pack(unsigned char out[48], const felem a){
  unsigned char tmp[48];
  for(int i=0; i<6; i++){
    for(int j=0; j<8; j++){
      tmp[8*i+j] = (a[i]>>(8*j)) & 0xff;
    }
  }
  for(int i=0; i<48; i++){
    out[i] = tmp[47-i];
  }
}

static void
unpack(felem a, const unsigned char in[48]){
  unsigned char tmp[48];
  for(int i=0; i<48; i++){
    tmp[i] = in[47-i];
  }
  for(int i=0; i<6; i++){
    a[i] = (uint64_t) tmp[8*i]
      | ((uint64_t)tmp[8*i+1] << 8)
      | ((uint64_t)tmp[8*i+2] << 16)
      | ((uint64_t)tmp[8*i+3] << 24)
      | ((uint64_t)tmp[8*i+4] << 32)
      | ((uint64_t)tmp[8*i+5] << 40)
      | ((uint64_t)tmp[8*i+6] << 48)
      | ((uint64_t)tmp[8*i+7] << 56);
  }
}

static void
mov(felem r, const felem a)
{
  for (int i = 0; i < 6; i++) {
    r[i] = a[i];
  }
}

static bool
equal(const felem a, const felem b)
{
  uint64_t d = 0;
  for(int i=0; i<6; i++){
    d |= (a[i]^b[i]);
  }
  return d==0;
}

static void
cmov(felem r, const felem a, uint64_t cond)
{
  uint64_t mask_mov;
  uint64_t mask_nomov;
  mask_mov = 1+~cond;
  mask_nomov = ~mask_mov;
  for(int i=0; i<6; i++){
    r[i] = (mask_nomov & r[i]) | (mask_mov & a[i]);
  }
}

static void
neg_conditional(felem r, const felem a, uint64_t cond)
{
  felem t;
  uint64_t mask_neg;
  uint64_t mask_orig;
  negate(t, a);
  mask_neg = 1+~cond;
  mask_orig = ~mask_neg;
  for(int i=0; i<6; i++){
    r[i] = (mask_neg & t[i]) | (mask_orig & a[i]);
  }
}

/* Representation independent arithmetic */
static void
to_mont(felem r, const felem a)
{
  mult(r, a, Rsqr);
}

static void
from_mont(felem r, const felem a)
{
  felem one = {1};
  mult(r, a, one);
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
/* Group operations */

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
      for(int i=0; i<6; i++){
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
  /* Remove pointless multiplications */
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
/* Scalar multiplication */

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
  for (int i = 0; i < 6; i++) {
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
    assert(oncurve(xQ, yQ, zQ, false));
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
  for(int i=0; i<6; i++){
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
p384_64_valid(unsigned char p[96])
{
  felem x;
  felem y;
  felem one = { 1 };
  unpack(x, p);
  unpack(y, p + 48);
  return oncurve(x, y, one, true);
}

void
p384_64_scalarmult(unsigned char q[96], const unsigned char n[48],
                   const unsigned char p[96])
{
  felem x;
  felem y;
  felem x_t;
  felem y_t;
  unpack(x, p);
  unpack(y, p + 48);
  scalarmult(x_t, y_t, x, y, n);
  pack(q, x_t);
  pack(q + 48, y_t);
}

void
p384_64_scalarmult_base(unsigned char q[96], const unsigned char n[48])
{
  felem x;
  felem y;
  felem one = {1};
  assert(oncurve(base_x, base_y, one, true));
  scalarmult(x, y, base_x, base_y, n);
  pack(q, x);
  unpack(x, q);
  pack(q + 48, y);
  unpack(x, q);
}

void
p384_64_double_scalarmult_base(unsigned char q[96], const unsigned char a[96], const unsigned char n1[48], const unsigned char n2[48]){
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
