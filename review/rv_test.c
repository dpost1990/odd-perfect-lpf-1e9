#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <gmp.h>
typedef unsigned __int128 u128;
#include "rv_funcs.inc"
int main(){ srand(4242); long bad=0,n=0;
  FILE *f=fopen("runs/lg2_samples.txt","w");
  for(int i=0;i<20000;i++){ uint64_t x = (i<3000)? (uint64_t)i+2 : 2+((((uint64_t)rand())<<31)^rand())%((1ULL<<62)); if(i%5==0) x=(1ULL<<(rand()%62)); if(x<2)x=2;
    fprintf(f,"%llu %llu %llu\n",(unsigned long long)x,(unsigned long long)lg2_bound(x,0),(unsigned long long)lg2_bound(x,1)); }
  fclose(f);
  mpz_t r,b,m; mpz_inits(r,b,m,NULL);
  for(int i=0;i<300000;i++){ uint64_t q=3+2*(rand()%1073741823ULL); uint64_t M=q*q; mont_t c; mont_init(&c,M);
    uint64_t base=((((uint64_t)rand())<<31)^rand()); uint64_t e=rand()%2000000000ULL; if(i%3==0){ /* force cases equal to 1 */ base=1; }
    mpz_set_ui(b,base); mpz_set_ui(m,M); mpz_powm_ui(r,b,e,m); int g=(mpz_cmp_ui(r,1)==0);
    n++; if(g!=pow_is_one_mod(base,e,&c)) bad++; }
  /* Wieferich-type known example: 3^(11-1) = 1 mod 11^2 */
  { mont_t c; mont_init(&c,121); n++; if(!pow_is_one_mod(3,5,&c)) bad++; mont_init(&c,1093ULL*1093); n++; if(!pow_is_one_mod(2,364,&c)) bad++; }
  for(int i=0;i<200000;i++){ uint64_t q=3+rand()%2000000000ULL; uint64_t a=rand()%q, e=rand(); mpz_set_ui(b,a); mpz_set_ui(m,q); mpz_powm_ui(r,b,e,m); n++; if(mpz_get_ui(r)!=pm(a,e,q)) bad++; }
  printf("rv_test: %ld checks, %ld failures\n",n,bad); return 0; }
