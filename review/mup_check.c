/* mup_check.c -- independent rigorous upper bound for M = prod_{p odd prime <= B} p/(p-1).
 * Different derivation from lpf.c / replay.py (which sum log-series and bound exp by Taylor):
 * here the product itself is formed, numerator and denominator separately, in integer "directed rounding"
 * floating point (64-bit mantissa, exact 128-bit products, rounded UP for prod p and DOWN for prod (p-1)).
 * Primes come from the primesieve library (independent of the sieves in lpf.c and replay.py).
 * Output: NUM_M NUM_E DEN_M DEN_E  with  M <= (NUM_M*2^NUM_E) / (DEN_M*2^DEN_E)  rigorously.
 * usage: mup_check B */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <primesieve.h>
typedef unsigned __int128 u128;
typedef struct { uint64_t m; int64_t e; } xf;
static inline xf xf_u64(uint64_t x){ xf r; int s=__builtin_clzll(x); r.m=x<<s; r.e=-(int64_t)s; return r; }
static inline xf xf_mul(xf a, xf b, int up){ xf r; u128 P=(u128)a.m*b.m; int sh=(P>>127)?64:63;
  uint64_t m=(uint64_t)(P>>sh); u128 rem=P&((((u128)1)<<sh)-1); r.e=a.e+b.e+sh;
  if(up&&rem){ m++; if(m==0){ m=1ULL<<63; r.e++; } } r.m=m; return r; }
int main(int argc,char**argv){
  uint64_t B=strtoull(argv[1],0,10);
  primesieve_iterator it; primesieve_init(&it);
  xf num=xf_u64(1), den=xf_u64(1); uint64_t p, cnt=0;
  while((p=primesieve_next_prime(&it))<=B){ if(p==2) continue; num=xf_mul(num,xf_u64(p),1); den=xf_mul(den,xf_u64(p-1),0); cnt++; }
  primesieve_free_iterator(&it);
  printf("%llu %lld %llu %lld %llu\n",(unsigned long long)num.m,(long long)num.e,(unsigned long long)den.m,(long long)den.e,(unsigned long long)cnt);
  return 0; }
