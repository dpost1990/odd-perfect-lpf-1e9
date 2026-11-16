/* unit test of the directed-rounding xf arithmetic used in lpf_exact.c, against exact GMP integers */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <gmp.h>
typedef unsigned __int128 u128;
typedef struct { uint64_t m; int64_t e; } xf;
static inline xf xf_u64(uint64_t x){ xf r; if(!x){ r.m=0; r.e=0; return r; } int s=__builtin_clzll(x); r.m=x<<s; r.e=-(int64_t)s; return r; }
static inline xf xf_mul(xf a, xf b, int up){
  xf r; if(!a.m||!b.m){ r.m=0; r.e=0; return r; }
  u128 P=(u128)a.m*b.m; int sh = (P>>127)? 64 : 63;
  uint64_t m=(uint64_t)(P>>sh); u128 rem = P & ((((u128)1)<<sh)-1);
  r.e=a.e+b.e+sh;
  if(up && rem){ m++; if(m==0){ m=1ULL<<63; r.e++; } }
  r.m=m; return r; }
static inline xf xf_pow(xf x, uint64_t n, int up){ xf r=xf_u64(1); while(n){ if(n&1) r=xf_mul(r,x,up); n>>=1; if(n) x=xf_mul(x,x,up); } return r; }
static inline int xf_lt(xf a, xf b){ if(!a.m) return b.m!=0; if(!b.m) return 0; if(a.e!=b.e) return a.e<b.e; return a.m<b.m; }
/* compare xf with exact integer z: returns sign(xf - z) */
static int xf_cmpz(xf a, mpz_t z){ mpz_t v; mpz_init_set_ui(v,a.m); int r;
  if(a.e>=0){ mpz_mul_2exp(v,v,a.e); r=mpz_cmp(v,z); } else { mpz_t zz; mpz_init(zz); mpz_mul_2exp(zz,z,-a.e); r=mpz_cmp(v,zz); mpz_clear(zz); }
  mpz_clear(v); return r; }
int main(){ srand(12345); long bad=0, n=0; mpz_t z; mpz_init(z);
  for(int it=0; it<200000; it++){
    uint64_t x = 2 + ((((uint64_t)rand())<<31) ^ rand()) % 2000000000ULL; if(it%7==0) x = 2+rand()%50; if(it%11==0) x=(1ULL<<(rand()%62))+ (rand()%3) - 1; if(x<2) x=2;
    uint64_t e = 1 + rand()% (it%3==0? 3000 : 40);
    mpz_ui_pow_ui(z,x,e);
    xf up=xf_pow(xf_u64(x),e,1), dn=xf_pow(xf_u64(x),e,0);
    n++; if(xf_cmpz(up,z)<0 || xf_cmpz(dn,z)>0){ bad++; if(bad<5) printf("BAD x=%llu e=%llu\n",(unsigned long long)x,(unsigned long long)e); }
    if((up.m>>63)!=1 || (dn.m>>63)!=1){ bad++; printf("not normalized\n"); }
  }
  /* products of several factors */
  for(int it=0; it<100000; it++){ xf u=xf_u64(1), d=xf_u64(1); mpz_set_ui(z,1); int k=1+rand()%60;
    for(int j=0;j<k;j++){ uint64_t x=2+((((uint64_t)rand())<<31)^rand())%4000000000ULL; u=xf_mul(u,xf_u64(x),1); d=xf_mul(d,xf_u64(x),0); mpz_mul_ui(z,z,x); }
    n++; if(xf_cmpz(u,z)<0 || xf_cmpz(d,z)>0) bad++; }
  /* xf_lt exactness on equal / adjacent values */
  for(uint64_t x=2;x<100000;x++){ xf a=xf_u64(x), b=xf_u64(x+1); n++; if(!xf_lt(a,b) || xf_lt(b,a) || xf_lt(a,a)) bad++; }
  printf("xf_test: %ld checks, %ld failures\n", n, bad); return bad!=0; }
