/* A constant time 32 bit implementation of P384             *
 * We use 64 bit words in our multiply and addition routines *
 * Can replace with assembler intrinsics. Heck, can do the   *
 * whole thing with assembler */

#include<stdint.h>
#include<stdbool.h>
#include<assert.h>
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
  assert((carry && pb) || !carry);
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

static void prod_red(felem r, uint32_t p[25]){ /* Broken why?*/
  uint64_t t;
  uint32_t carry;
  uint32_t m;
  for(int i=0; i<12; i++){
    m=p[i];
    carry=0;
    for(int j=0; j<12; j++){ /* This adds a multiple of prime that makes p[i] zero */
      t = (uint64_t)p[i+j]+((uint64_t)m)*prime[j]+carry;
      p[i+j] = (uint32_t)(t & mask_lo);
      carry = t >> 32;
    }
    for(int j=12+i; j<25; j++){
      t = (uint64_t)p[j]+carry;
      p[j] = (uint32_t) (t & mask_lo);
      carry = t >> 32;
    }
  }
  for(int i=0; i<12; i++){
    r[i] = p[12+i];
  }
  reduce_add_sub(r, p[24]);
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

static void mult_nored(uint32_t prod[25], const felem a, const felem b){
  uint64_t t;
  uint32_t carry;
  for(int i=0; i<25; i++){
    prod[i]=0;
  }
  for(int i=0; i<12; i++){ /*TODO: check correctness */
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

static void unpack(felem r, unsigned char *in){
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

/* Operations on the curve in Jacobian coordinates using readditions */


/* Total operations for verification */

/* Table based multiplication routines */

/* Interface to outside world */

/* Test routine: called main because I am lazy */
int main(){
  felem a;
  felem b;
  felem c;
  felem d;
  felem e;
  felem f;
  felem t;
  for(int i=0; i<12; i++){
    a[i]=0;
    b[i]=0;
    c[i]=0;
    d[i]=0;
    e[i]=0;
    f[i]=0;
    t[i]=0;
  }
  printval("prime", prime);
  printval("R", R);
  printf("print R == 2**384 %% prime\n");
  printval("primes2", primes2);
  printf("print prime-2 == primes2\n");
  a[0]=15;
  a[11]=47;
  a[3]=5;
  unsigned char out[48];
  unsigned char out2[48];
  to_mont(c, a);
  from_mont(b, c);
  pack(out, b);
  pack(out2, a);
  if(memcmp(out2, out, 48)){
    printf("print montround: False \n");
  }
  mult(c, a, b);
  printval("c_old", c);
  printval("a_old", a);
  printval("b_old", b);
  printval("t_old", t);
  printf("print c_old*R %% prime == a_old*b_old %% prime\n");
  inv(d, b);
  printval("a", a);
  printval("b", b);
  printval("c", c);
  printval("t", t);
  printf("print \"id c: \", c_old == c\n");
  printf("print \"id b: \", b_old == b\n");
  printf("print \"id a: \", a_old == a \n");
  printf("print \"id t: \", t_old == t \n");
  mult(e, b, d);
  mult(f, c, d);
  mult(t, a, R);
  printval("d", d);
  printval("e", e);
  printval("f", f);
  printval("t", t);
  printf("print c*R %% prime == a*b %% prime\n");
  printf("print e %% prime == R %% prime\n");
  printf("print f*R %% prime == c*d %% prime\n");
  printf("print f %% prime == a %% prime \n");
  printf("print t %% prime == a %% prime \n");
}
