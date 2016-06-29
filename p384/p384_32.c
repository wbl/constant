/* A constant time 32 bit implementation of P384             *
 * We use 64 bit words in our multiply and addition routines *
 * Can replace with assembler intrinsics. Heck, can do the   *
 * whole thing with assembler */

#include<stdint.h>
#include<stdbool.h>
#include<stdio.h>
#include<string.h>
#include "p384_32.h"


/* Constants */
/* We use little-endian arrays */
static const uint32_t prime[12] = {0xffffffff,
				   0x0,
				   0x0,
				   0xffffffff,
				   0xfffffffe,
				   0xffffffff,
				   0xffffffff,
				   0xffffffff,
				   0xffffffff,
				   0xffffffff,
				   0xffffffff,
				   0xffffffff};
static const uint32_t primes2[12] = {0xfffffffd,
				     0x0,
				     0x0,
				     0xffffffff,
				     0xfffffffe,
				     0xffffffff,
				     0xffffffff,
				     0xffffffff,
				     0xffffffff,
				     0xffffffff,
				     0xffffffff,
                                     0xffffffff};
static uint64_t mask_lo = 0x00000000ffffffff;

static const uint32_t Rsqr[12] = {0x1,
				  0xfffffffe,
				  0x0,
				  0x2,
				  0x0,
				  0xfffffffe,
				  0x0,
				  0x2,
				  0x1,
				  0x0,
				  0x0,
                                  0x0};
static const uint32_t R[12]={0x1,
			     0xffffffff,
			     0xffffffff,
			     0x0,
			     0x1,
			     0x0,
			     0x0,
			     0x0,
			     0x0,
			     0x0,
			     0x0,
                             0x0};

static const uint32_t curve_b[12]={0xd3ec2aef,
				   0x2a85c8ed,
				   0x8a2ed19d,
				   0xc656398d,
				   0x5013875a,
				   0x314088f,
				   0xfe814112,
				   0x181d9c6e,
				   0xe3f82d19,
				   0x988e056b,
				   0xe23ee7e4,
				   0xb3312fa7};
static const uint32_t base_x[12] ={0x72760ab7,
				   0x3a545e38,
				   0xbf55296c,
				   0x5502f25d,
				   0x82542a38,
				   0x59f741e0,
				   0x8ba79b98,
				   0x6e1d3b62,
				   0xf320ad74,
				   0x8eb1c71e,
				   0xbe8b0537,
				   0xaa87ca22};
static const uint32_t base_y[12]={0x90ea0e5f,
				  0x7a431d7c,
				  0x1d7e819d,
				  0xa60b1ce,
				  0xb5f0b8c0,
				  0xe9da3113,
				  0x289a147c,
				  0xf8f41dbd,
				  0x9292dc29,
				  0x5d9e98bf,
				  0x96262c6f,
				  0x3617de4a};
/* Arithmetic */
typedef uint32_t felem[12];
/*Debug function */
static void printval(char *name, const felem val){
  printf("%s = ", name);
  for(int i=0; i<11; i++){
    printf("2**(32*%u)*%u+", i, val[i]);
  }
  printf("2**(32*11)*%u\n", val[11]);
}

static void printmulval(char *name, const uint32_t val[25]){
  printf("%s = ", name);
  for(int i=0; i<24; i++){
    printf("2**(32*%u)*%u+", i, val[i]);
  }
  printf("2**(32*24)*%u\n", val[24]);
}

static void reduce_add_sub(felem r, uint32_t carry){
  uint64_t t;
  uint32_t d[12];
  uint32_t b = 0;
  uint32_t pb = 0;
  uint32_t do_sub;
  uint32_t mask_sub;
  uint32_t mask_nosub;
  /* Now need to compare r and carry to prime, and if greater subtract in constant time */
  for(int i=0; i<12; i++){
    t = (uint64_t) prime[i]+pb;
    b = r[i]< t;
    t = r[i]-t+((uint64_t)b<<32);
    d[i]=(uint32_t) t & mask_lo;
    pb = b;
  }
  /* It should be the case that we only potentially need one subtraction. So if carry is set, should have pb set */
  /* Will do target tests (somehow: need to expose more internals. Or use test routines here)*/
  do_sub = 1 - ((carry+pb)&0x01);
  mask_sub = (uint32_t) -do_sub; //assume 2's complement
  mask_nosub = ~ mask_sub;
  for(int i=0; i<12; i++){
    r[i] = (mask_nosub & r[i]) | (mask_sub & d[i]);
  }
}

static void add(felem r, const felem a, const felem b){
  uint32_t carry = 0;
  uint64_t t;
  /* This part should be done with add/adc or replaced with asm loop if we want to go per-cpu */
  for(int i=0; i<12; i++){
    t = (uint64_t) a[i] + (uint64_t) b[i] + carry;
    r[i] = (uint32_t) (t&mask_lo);
    carry = t >> 32;
  }
  reduce_add_sub(r, carry);
}

static void sub(felem r, const felem a, const felem b){ /* Will need testing*/
  uint32_t carry = 0;
  uint64_t t=0;
  uint32_t brw=0;
  uint32_t pbrw=0;
  for(int i=0; i<12; i++){ /* Assembler would be great for this.*/
    t = (uint64_t) prime[i]+a[i]+carry;
    brw = t < ((uint64_t)b[i])+pbrw;
    t += ((uint64_t)brw)<<32;
    t -= (uint64_t) b[i] + (uint64_t) pbrw;
    r[i] = (uint32_t) (t & mask_lo);
    carry = t >> 32;
    pbrw = brw;
  }
  reduce_add_sub(r, carry);
}

static void prod_red(felem r, uint32_t p[25]){
  uint64_t t;
  uint32_t carry;
  uint32_t delayed[13]={0};
  uint32_t m;
  for(int i=0; i<12; i++){
    m=p[i];
    carry=0;
    for(int j=0; j<12; j++){ /* This adds a multiple of prime that makes p[i] zero */
      t = (uint64_t)p[i+j]+((uint64_t)m)*prime[j]+carry;
      p[i+j] = (uint32_t)(t & mask_lo);
      carry = t >> 32;
    }
    delayed[i]=carry;
  }
  carry=0;
  for(int i=0; i<12; i++){
    t = ((uint64_t)p[i+12])+carry+delayed[i];
    r[i] = t & mask_lo;
    carry = t>>32;
  }
  reduce_add_sub(r, delayed[12]+p[24]+carry);
}

/* Question: how to multiply by 2, 3, and 8? A: 2 is easy, as is 3. For 8 multiply by 2 four times*/
static void mul2( felem c, const felem a){
  add(c, a, a);
}
static void mul3(felem c, const felem a){
  mul2(c, a);
  add(c, c, a);
}

static void mul4(felem c, const felem a){
  mul2(c, a);
  mul2(c, c);

}

static void mul8(felem c, const felem a){
  felem t;
  mul2(c, a);
  mul2(t, c);
  mul2(c, t);
}

static void mult_nored(uint32_t prod[25], const felem a, const felem b){
  uint64_t t;
  uint32_t carry;
  for(int i=0; i<25; i++){
    prod[i]=0;
  }
  for(int i=0; i<12; i++){ /*TODO: Karastuba?*/
    carry = 0;
    for(int j=0; j<12; j++){
      t = ((uint64_t) a[i])*b[j]+carry+prod[i+j];
      prod[i+j] = (uint32_t) (t & mask_lo);
      carry = t >> 32;
    }
    prod[12+i]=carry;
  }
}

static void mult(felem r, const felem a, const felem b){
  uint32_t prod[25];
  mult_nored(prod, a, b);
  prod_red(r, prod);
}

static void sqr(felem r, const felem a){ /* Doesn't seem to help very much*/
  uint32_t prod[25];
  uint64_t t;
  uint32_t carry;
  for(int i=0; i<25; i++){
    prod[i]=0;
  }
  
  for(int i=0; i<12; i++){
    carry = 0;
    for(int j=i+1; j<12; j++){
      t = ((uint64_t) a[i])*a[j]+carry+prod[i+j];
      prod[i+j] = (uint32_t) (t & mask_lo);
      carry = t >> 32;
    }
    prod[12+i]=carry;
  }
  carry=0;
  for(int i=0; i<25; i++){
    t = ((uint64_t) prod[i])*2+carry;
    prod[i] = (uint32_t) t;
    carry = t >> 32;
  }
  carry=0;
  for(int i=0; i<12; i++){
    t=((uint64_t) a[i])*a[i]+carry+prod[2*i];
    prod[2*i] = t & mask_lo;
    carry = t >> 32;
    t = ((uint64_t) prod[2*i+1])+carry;
    prod[2*i+1] = t & mask_lo;
    carry = t>>32;
  }
  prod_red(r, prod);
}

/* Now for some packing and unpacking */
/* These don't do conversion */
static void pack(unsigned char *out, const felem r){ /*Big endian*/
  for(int i=0; i<12; i++){
    out[4*(11-i)+3] = r[i] & 0xff;
    out[4*(11-i)+2] = (r[i]>>8) & 0xff;
    out[4*(11-i)+1] = (r[i]>>16) & 0xff;
    out[4*(11-i)] = (r[i]>>24) & 0xff;
    
  }
}

static void unpack(felem r, const unsigned char *in){
  for(int i=0; i<12; i++) {
    r[i] = in[4*(11-i)] << 24|
      in[4*(11-i)+1] << 16|
      in[4*(11-i)+2] << 8 |
      in[4*(11-i)+3];
  }
}

static void to_mont(felem r, const felem a){
  mult(r, a, Rsqr);
}

static void from_mont(felem r, const felem a){
  felem one = {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
  mult(r, a, one);
}
/* And we need to invert in the field via CRT. */
/* Solution: simple double and add (for now) */
static void inv(felem r, const felem a){ /* Cannot be in place */
   for(int i=0; i<12; i++){
    r[i]=R[i];
  }
  for(int i=11; i>=0; i--){ /* start at the high value bit*/
    for(int j=31; j>=0; j--){
      mult(r, r, r);
      if((primes2[i]>>j) & 0x1){
	mult(r, r, a);
      }
    }
  }
  
}
static bool equal(const felem a, const felem b){ //Can leak *result*
  uint32_t diff = 0;
  for(int i=0; i<12; i++){
    diff |= a[i] ^ b[i];
  }
  return diff == 0;
}

static bool iszero(const felem a){
  uint32_t test = 0;
  for(int i=0; i<12; i++){
    test |= a[i];
  }
  return test ==0;
}

static void neg_conditional(felem r, const felem a, uint32_t cond){ /* Should try in-place*/
  uint32_t diff[12];
  uint32_t pbrw = 0;
  uint32_t brw = 0;
  uint64_t t;
  uint32_t mask_diff;
  uint32_t mask_nodiff;
  for(int i=0; i<12; i++){
    t = (uint64_t) prime[i];
    brw = t < (uint64_t)a[i]+pbrw;
    t += (uint64_t) brw << 32;
    t -= (uint64_t) a[i] + pbrw;
    diff[i] = (uint32_t) (t & mask_lo); /* There is no carry because a<prime */
  }
  mask_diff = (uint32_t) -cond;
  mask_nodiff = ~mask_diff;
  for(int i=0; i<12; i++){
    r[i] = (diff[i]&mask_diff) |(a[i] &mask_nodiff);
  }
}

static void mov(felem r, const felem a){
  for(int i=0; i<12; i++){
    r[i]=a[i];
  }
}

static void cmov(felem r, const felem a, uint32_t cond){
  uint32_t mask_set;
  uint32_t mask_unset;
  mask_set = (uint32_t) -cond;
  mask_unset = ~ mask_set;
  for(int i=0; i<12; i++){
    r[i] = (r[i]&mask_unset)|(a[i]&mask_set);
  }
}
  
/* Operations on the curve in Jacobian coordinates using readditions */
/* We do not implement a specialized affine addition because inversion is slow (can fix) */
/* The point at infinity is exceptional and leaks. To deal with this we use a signed form of exponents*/

static bool oncurve(const felem x, const felem y, const felem z, bool not_mont){ //not montgomery
  felem z2, z4, z6, t0, t1,t2, t3, t4, t5, ysqr, rhs, bmont, xm, ym, zm;
  to_mont(bmont, curve_b);
  if(not_mont){
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

static void double_pt(felem x3, felem y3, felem z3, const felem x1, const felem y1, const felem z1){
  /* As the order is not divisible by 2, impossible to double finite point and get infinity */
  /* Also works for point at infinity (assuming correct representation */
  /* TODO: color */
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
  sqr(delta, z1); //specialize square after working
  sqr(gamma, y1);
  mult(beta, x1, gamma);
  sub(t0, x1, delta);
  add(t1, x1, delta);
  mult(t2, t0, t1);
  mul3(alpha, t2);
  sqr(t3, alpha);
  mul8(t4, beta);
  sub(x3, t3, t4);
  add(t5, y1, z1);
  sqr(t6, t5);
  sub(t7, t6, gamma);
  sub(z3, t7, delta);
  mul4(t8, beta);
  sub(t9, t8, x3);
  sqr(t10, gamma);
  mul8(t11, t10);
  mult(t12, alpha, t9);
  sub(y3, t12, t11);
}

static void add_pt_tot(felem x3, felem y3, felem z3, const felem x1, const felem y1, const felem z1, const felem x2, const felem y2, const felem z2){
  /* Special cases: z1 or z2 zero=> return the other point
     if we are doubling: use the doubling.
     if we produce infinity: set the output correctly */
  /* Uses add-2007-bl. Note that test z1, z2, for pt at infinity (so return other one) and H for either double or inverse (return infinity)*/
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
  if(iszero(z1)){
    mov(x3, x2);
    mov(y3, y2);
    mov(z3, z2);
    return;
  }else if(iszero(z2)){
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
  if(iszero(h)){
    if(equal(s1,s2)){
      double_pt(x3, y3, z3, x1, y1, z1);
      return;
    }else{
      for(int k=0; k<12; k++){
	x3[k]=0;
	y3[k]=0;
	z3[k]=0;
      }
      x3[0]=1;
      y3[0]=1;
      return;
    }
  }
  mul2(t2, h);
  mult(i, t2, t2);
  mult(j, h, i);
  sub(t2, s2, s1);
  mul2(r, t3);
  mult(v, u1, i);
  mult(t4, r, r);
  mul2(t5, v);
  sub(t6, t4, j);
  sub(x3, t6,t5);
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

static void add_pt_const(felem x3, felem y3, felem z3, const felem x1, const felem y1, const felem z1, const felem x2, const felem y2, const felem z2){
  /* Produces junk if used to add a point to itself or points at infinity. This is ok: we use flags and constant time moves*/
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
  sqr(z1z1, z1);
  sqr(z2z2, z2);
  mult(u1, z2z2, x1);
  mult(u2, z1z1, x2);
  mult(t0, z2, z2z2);
  mult(s1, y1, t0);
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
  sub(x3, t6,t5);
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

static void readd_pt_const(felem x3, felem y3, felem z3, const felem x1, const felem y1, const felem z1, const felem x2, const felem y2, const felem z2, const felem z2z2, const felem z2z2z2){
  /* Produces junk if used to add a point to itself or points at infinity. This is ok: we use flags and constant time moves*/
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
  felem z2z2_recalc;
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
  sub(x3, t6,t5);
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

static void to_affine(felem x2, felem y2, const felem x1, const felem y1, const felem z1){
  felem zr;
  felem zrzr;
  inv(zr, z1);
  mult(zrzr, zr, zr);
  mult(x2, x1, zrzr);
  mult(zr, zrzr, zr);
  mult(y2, y1, zr);
}


static void scalarmult(felem x_out, felem y_out, const felem x_in, const felem y_in, const unsigned char key[48]){
  felem xm;
  felem ym;
  bool correct;
  /*Note, we need to make sure that the key is < order for correctness */
  /* For now double and add. Tables and signed NAF later */
  /* Remember z==1, in montgomery form is R */
  to_mont(xm, x_in);
  to_mont(ym, y_in);
  felem xQ, yQ, zQ;
  felem xR, yR, zR;
  felem xT, yT, zT,zzT, zzzT;
  felem table[16][5];
  for(int i=0; i<12; i++){
    xQ[i]=0;
    yQ[i]=0;
    zQ[i]=0;
  }
  mov(xQ, R);
  mov(yQ, R); //Q is pt at infinity
  mov(table[1][0], xm);
  mov(table[1][1], ym);
  mov(table[1][2], R);
  sqr(table[1][3], table[1][2]);
  mult(table[1][4], table[1][2], table[1][3]);
  for(int i=2; i<16; i++){
    if(i %2 == 1){
      add_pt_const(table[i][0], table[i][1], table[i][2], table[i-1][0], table[i-1][1], table[i-1][2],
		   xm, ym, R);
    }else{
      double_pt(table[i][0], table[i][1], table[i][2], table[i/2][0], table[i/2][1], table[i/2][2]);
    }
    sqr(table[i][3], table[i][2]);
    mult(table[i][4], table[i][3], table[i][2]);
  }
  bool first = 1;
  bool seen_1 = 0;
  for(int i=47; i>=0; i--){ //little-endian
    for(int j=4; j>=0; j-=4){
      if(!first){
	double_pt(xQ, yQ, zQ, xQ, yQ, zQ);
	double_pt(xQ, yQ, zQ, xQ, yQ, zQ);
	double_pt(xQ, yQ, zQ, xQ, yQ, zQ);
	double_pt(xQ, yQ, zQ, xQ, yQ, zQ);
      }
      first = 0;
      int index = (key[i]>>j) & 0xf;
      int valid_point = (index!=0); //check constant time
      for(int k=0; k<16; k++){
	cmov(xT, table[k][0], k==index);
	cmov(yT, table[k][1], k==index);
	cmov(zT, table[k][2], k==index);
	cmov(zzT, table[k][3], k==index);
	cmov(zzzT, table[k][4], k==index);
      }
      readd_pt_const(xR, yR, zR, xQ, yQ, zQ, xT, yT, zT, zzT, zzzT);
      cmov(xR, xT, (1-seen_1));
      cmov(yR, yT, (1-seen_1));
      cmov(zR, zT, (1-seen_1));
      seen_1 = seen_1 | valid_point;
      cmov(xQ, xR, valid_point);
      cmov(yQ, yR, valid_point);
      cmov(zQ, zR, valid_point);
    }
  }
  to_affine(x_out, y_out, xQ, yQ, zQ);
  from_mont(x_out, x_out);
  from_mont(y_out, y_out);
}

/* Interface to outside world */
bool p384_32_valid(unsigned char p[96]){
  felem x;
  felem y;
  felem one = {1};
  unpack(x, p);
  unpack(y, p+48);
  return oncurve(x, y, one, true);
}

void p384_32_scalarmult(unsigned char q[96], const unsigned char n[48], const unsigned char p[96]){
  felem x;
  felem y;
  unpack(x, p);
  unpack(y, p+48);
  felem one = {1};
  if(!oncurve(x, y, one, true)){
    p384_32_scalarmult_base(q, n);
  }else{
    scalarmult(x, y, x, y, n);
    pack(q, x);
    pack(q+48, y);
  }
}

void p384_32_scalarmult_base(unsigned char q[96], const unsigned char n[48]){
  felem x;
  felem y;
  scalarmult(x, y, base_x, base_y, n);
  pack(q, x);
  pack(q+48, y);
}
