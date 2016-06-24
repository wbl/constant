/* A constant time 32 bit implementation of P384             *
 * We use 64 bit words in our multiply and addition routines *
 * Can replace with assembler intrinsics. Heck, can do the   *
 * whole thing with assembler */

#include<stdint.h>
#include<stdbool.h>
#include<assert.h>
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
				  0x0};


/* Arithmetic */
typedef uint32_t felem[12];

static void reduce_add_sub(felem r, uint32_t carry){
  uint64_t t;
  uint32_t d[12];
  uint32_t b = 0;
  uint32_t pb = 0;
  uint32_t nb = 0;
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
  assert((carry && pb) || !carry);
  pb -= carry;
  nb = 1 - pb;
  mask_sub = (uint32_t) -nb; //assume 2's complement
  mask_nosub = (uint32_t) -pb;
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

static void sub(felem r, const felem a, const felem b){
  uint32_t carry = 0;
  uint64_t t;
  uint32_t brw;
  uint32_t pbrw;
  for(int i=0; i<12; i++){ /* Assembler would be great for this.*/
    t = (uint64_t) prime[i]+a[i]+carry;
    brw = t < b[i]+pbrw;
    t += (uint64_t)brw<<32;
    t -= (uint64_t) b[i] + (uint64_t) pbrw;
    r[i] = (uint32_t) (t & mask_lo);
    carry = t >> 32;
    pbrw = brw;
  }
  /* We know that there is no borrow here because we added p*/
  reduce_add_sub(r, carry);
}

static void mont_red(felem r, uint32_t p[24]){ /* Does a clobber */
  uint32_t carry =0;
  uint64_t t;
  uint32_t d;
  for(int i=0; i<12; i++){
    d=p[i];
    for(int j=0; j<12; j++){
      t = (uint64_t)p[i+j]+d*prime[j]+carry;
      p[i+j] = t & mask_lo;
      carry = t >> 32;
    }
  }
  for(int i=0; i<12; i++){
    r[i] = p[12+i];
  }
  reduce_add_sub(r, 0);
}

/* Question: how to multiply by 2, 3, and 8? A: 2 is easy, as is 3. For 8 multiply by 2 four times*/
static void mul2( felem c, felem a){
  add(c, a, a);
}
static void mul3(felem c, felem a){
  mul2(c, a);
  add(c, c, a);
}

static void mul8(felem c, felem a){
  felem t;
  mul2(c, a);
  mul2(t, c);
  mul2(c, t);
}

static void mult(felem r, const felem a, const felem b){
  uint32_t prod[24];
  uint64_t t;
  uint32_t carry;
  for(int i=0; i<24; i++){
    prod[i]=0;
  }
  for(int i=0; i<12; i++){ /*TODO: optimize */
    carry = 0;
    for(int j=0; j<12; j++){
      t = (uint64_t) a[i]*b[j]+carry+prod[i+j];
      prod[i+j] = (uint32_t) (t & mask_lo);
      carry = t >> 32;
    }
    prod[12+i]=carry;
  }
  mont_red(r, prod);
}

/* Now for some packing and unpacking */
/* These also do conversion */
static void pack(unsigned char *out, felem r){ /*Big endian*/
  uint32_t tmp[24]; /*Need to divide by R */
  uint32_t space[12];
  for(int i=0; i<12; i++){
    tmp[12+i] = 0;
    tmp[i] = r[i];
  }
  mont_red(space, tmp);
  for(int i=0; i<12; i++){
    for(int j=0; j<4; j++){
      out[4*(11-i)+j]=space[i]>>(24-8*j) & 0xff;
    }
  }
}

static void unpack(felem r, unsigned char *in){
  felem tmp;
  for(int i=0; i<12; i++) {
    tmp[i] = in[4*(11-i)] |
      in [4*(11-i)+1] << 8 |
      in [4*(11-i)+2] << 16 |
      in [4*(11-i)+3] << 24;
  }
  mult(r, tmp, Rsqr);
}

/* And we need to invert in the field via CRT. */
/* Solution: simple double and add */
static void inverse(felem r, felem a){
  felem t;
}
/* Operations on the curve in Jacobian coordinates using readditions */


/* Total operations for verification */

/* Table based multiplication routines */

/* Interface to outside world */
