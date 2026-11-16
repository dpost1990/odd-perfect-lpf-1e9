/*
 * lpf.c -- exhaustive sigma-closure search:
 *     find ALL N > 1 with every prime factor <= B and  sigma(N) = (kn/kd) * N
 *     (mode "odd": N odd; mode "even": 2 allowed in N).
 * For kn/kd = 2 and mode odd, "no solution" proves: every odd perfect number has a prime factor > B.
 *
 * Mathematics (see README.md for the full argument):
 *  - sigma(p^a) = prod_{d | a+1, d > 1} Phi_d(p).
 *  - Every prime factor q of Phi_d(p) satisfies ord_q(p) = d, or q | d (then q = P(d), the largest prime of d,
 *    and v_q(Phi_d(p)) = 1 when d > 2).
 *  - Bang-Zsigmondy: for d >= 3 (and d = 2 unless p+1 is a power of 2; and except p=2,d=6) Phi_d(p) has a
 *    prime q with ord_q(p) = d.  Since sigma(N) = kN is B-smooth, d must be ord_q(p) of an allowed q <= B.
 *  - "Row" of p: ord_q(p) for every allowed prime q <= B.  d is GOOD iff Phi_d(p) factors completely over the
 *    allowed primes; exponent a is admissible iff every divisor e > 1 of a+1 is good.
 *  - Size filter (sound, only rejects): if  sum_{q: ord_q(p)=d} v_q log q + log P(d)  <  phi(d) log(p-1) - 1
 *    then Phi_d(p) (> (p-1)^phi(d)) cannot be smooth.  For large orders o the bucket is bounded by
 *    #{q <= B : q = 1 mod o} <= (B-1)/o primes with v_q = 1 unless the Wieferich-type test p^o = 1 mod q^2 fires.
 *  - DFS identical to closure_solver.py; all pruning decisions use exact integer arithmetic (GMP); the
 *    abundancy upper bound uses a rigorous rational upper bound M_up >= prod_{p in P} p/(p-1).
 *
 * usage: lpf B kn/kd odd|even threads rowcache logfile
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <pthread.h>
#include <time.h>
#include <gmp.h>
#include <unistd.h>

typedef unsigned __int128 u128;
static uint64_t B; static int ODD; static long KN, KD; static int NTH;
static uint32_t *pr; static size_t npr;           /* all primes <= B, pr[0]=2 */
static uint8_t *obits;                             /* bit i set <=> 2i+1 prime */
static uint8_t *fcnt; static uint16_t *flist; static uint64_t *fofs; /* q-1 small odd factors per prime index */
#define FCH 4096
static double LNB;
static FILE *LOG; static FILE *CACHE;
static double T0;
static double now(){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec; }
static inline int isprime_odd(uint64_t n){ return (n&1) && n<=B && ((obits[n>>4]>>((n>>1)&7))&1); }
static int isprime_any(uint64_t n){ if(n==2) return B>=2; if(n<3||n>B) return 0; return isprime_odd(n); }
static long pidx(uint64_t p){ size_t lo=0,hi=npr; while(lo<hi){size_t m=(lo+hi)/2; if(pr[m]<p) lo=m+1; else hi=m;} return (lo<npr&&pr[lo]==p)?(long)lo:-1; }

/* ---------------- sieve + q-1 factor table ---------------- */
static void build_tables(void){
  uint64_t nb=(B>>4)+2; obits=calloc(nb,1);
  uint64_t r=(uint64_t)sqrt((double)B)+2; while(r*r>B) r--;
  uint8_t *small=calloc(r+2,1); /* composite flags up to r */
  for(uint64_t i=2;i*i<=r;i++) if(!small[i]) for(uint64_t j=i*i;j<=r;j+=i) small[j]=1;
  uint32_t *bp=malloc(sizeof(uint32_t)*(r+1)); size_t nbp=0;
  for(uint64_t i=3;i<=r;i+=2) if(!small[i]) bp[nbp++]=i;
  const uint64_t S=1<<20; uint8_t *seg=malloc(S);
  for(uint64_t L=1; L<=B; L+=2*S){ /* odd numbers L, L+2, ..., covers [L, L+2S) */
    memset(seg,1,S);
    for(size_t k=0;k<nbp;k++){ uint64_t p=bp[k]; if(p*p>=L+2*S) break;
      uint64_t st=p*p; if(st<L){ st=((L+p-1)/p)*p; if(!(st&1)) st+=p; }
      for(uint64_t j=st;j<L+2*S;j+=2*p) seg[(j-L)>>1]=0; }
    for(uint64_t i=0;i<S;i++){ uint64_t n=L+2*i; if(n>B) break; if(n==1) continue; if(seg[i]) obits[n>>4]|=1<<((n>>1)&7); }
  }
  free(seg);
  /* prime list */
  size_t cap=1<<20; pr=malloc(4*cap); npr=0; if(B>=2) pr[npr++]=2;
  for(uint64_t n=3;n<=B;n+=2) if(isprime_odd(n)){ if(npr==cap){cap*=2; pr=realloc(pr,4*cap);} pr[npr++]=n; }
  /* factor table: for prime index i>=1 (odd q), odd prime factors < 65536 of q-1 */
  fcnt=calloc(npr,1); fofs=malloc(8*(npr/FCH+2));
  size_t fcap=npr*3+16, fn=0; flist=malloc(2*fcap);
  uint32_t lp[6600]; size_t nlp=0; for(size_t k=1;k<npr && pr[k]<65536;k++) lp[nlp++]=pr[k];
  const uint64_t SS=1<<16; uint8_t *sc=calloc(SS,1); uint16_t (*sl)[12]=malloc(sizeof(uint16_t)*12*SS);
  size_t pi=1; /* next prime index to fill */
  for(uint64_t L=0; L<B; L+=SS){ /* n in [L, L+SS), n = q-1 */
    memset(sc,0,SS);
    for(size_t k=0;k<nlp;k++){ uint64_t l=lp[k]; uint64_t st=((L+2*l-1)/(2*l))*(2*l); if(st==0) st=2*l;
      for(uint64_t n=st;n<L+SS;n+=2*l){ uint64_t i=n-L; if(sc[i]<12) sl[i][sc[i]++]=(uint16_t)l; } }
    while(pi<npr && pr[pi]-1 < L+SS){ uint64_t n=pr[pi]-1; uint64_t i=n-L;
      if(pi%FCH==0) fofs[pi/FCH]=fn;
      if(fn+12>fcap){ fcap*=2; flist=realloc(flist,2*fcap); }
      fcnt[pi]=sc[i]; for(int c=0;c<sc[i];c++) flist[fn++]=sl[i][c];
      pi++; }
  }
  if(0%FCH==0) fofs[0]=0;
  free(sc); free(sl); free(small); free(bp);
}

/* ---------------- Montgomery arithmetic ---------------- */
static inline uint32_t m32inv(uint32_t m){ uint32_t x=m; for(int i=0;i<5;i++) x*=2-m*x; return -x; }
static inline uint32_t mm32(uint32_t a,uint32_t b,uint32_t m,uint32_t mi){ uint64_t t=(uint64_t)a*b; uint32_t u=(uint32_t)t*mi; uint64_t s=(t+(uint64_t)u*m)>>32; return s>=m? (uint32_t)(s-m):(uint32_t)s; }
static inline uint32_t pw32(uint32_t bm,uint64_t e,uint32_t one,uint32_t m,uint32_t mi){ uint32_t r=one; while(e){ if(e&1) r=mm32(r,bm,m,mi); e>>=1; if(e) bm=mm32(bm,bm,m,mi);} return r; }
static inline uint64_t m64inv(uint64_t m){ uint64_t x=m; for(int i=0;i<6;i++) x*=2-m*x; return -x; }
static inline uint64_t mm64(uint64_t a,uint64_t b,uint64_t m,uint64_t mi){ u128 t=(u128)a*b; uint64_t u=(uint64_t)t*mi; u128 s=(t+(u128)u*m)>>64; return s>=m? (uint64_t)(s-m):(uint64_t)s; }
static inline uint64_t tomont64(uint64_t a,uint64_t m){ a%=m; for(int i=0;i<64;i++){ a<<=1; if(a>=m) a-=m; } return a; } /* m < 2^63 */
static inline int pow_is_one_q2(uint64_t p,uint64_t e,uint64_t q){ /* p^e == 1 mod q^2 ? */
  uint64_t m=q*q, mi=m64inv(m); uint64_t one=(0-m)%m /* 2^64 mod m */, bm=(uint64_t)((((u128)(p%m))<<64)%m), r=one;
  while(e){ if(e&1) r=mm64(r,bm,m,mi); e>>=1; if(e) bm=mm64(bm,bm,m,mi);} return r==one; }
static uint64_t powmod64(uint64_t b,uint64_t e,uint64_t m){ uint64_t r=1%m; b%=m; while(e){ if(e&1) r=(u128)r*b%m; b=(u128)b*b%m; e>>=1;} return r; }

/* ---------------- exact directed-rounding "floats" (review copy) ----------------
 * xf = m * 2^e with m an integer in [2^63, 2^64) (or m = 0).  mul_up / mul_down round the exact 128-bit product
 * of the mantissas up / down to 64 bits, so every result is a rigorous upper / lower bound of the exact value.
 * Only integer operations are used: no floating point anywhere in the filters of this copy. */
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
static inline int xf_lt(xf a, xf b){ /* exact a < b for normalized values */
  if(!a.m) return b.m!=0; if(!b.m) return 0; if(a.e!=b.e) return a.e<b.e; return a.m<b.m; }

/* ---------------- small number theory ---------------- */
static int pfac(uint64_t n, uint64_t *f){ int k=0; for(uint64_t d=2; d*d<=n; d+= (d==2?1:2)) if(n%d==0){ f[k++]=d; while(n%d==0) n/=d; } if(n>1) f[k++]=n; return k; }
static uint64_t phi_of(uint64_t n){ uint64_t f[16]; int k=pfac(n,f); uint64_t r=n; for(int i=0;i<k;i++) r=r/f[i]*(f[i]-1); return r; }
static int mobius(uint64_t n){ uint64_t f[16]; int k=pfac(n,f); for(int i=0;i<k;i++) if((n/f[i])%f[i]==0) return 0; return (k&1)?-1:1; }

/* target valuations v_q(k) for q | kn*kd */
static int nkv; static uint64_t kvp[32]; static int kvv[32];
static int kval(uint64_t q){ for(int i=0;i<nkv;i++) if(kvp[i]==q) return kvv[i]; return 0; }
static int is_kprime(uint64_t q){ for(int i=0;i<nkv;i++) if(kvp[i]==q) return 1; return 0; }
static int in_P(uint64_t q){ if(q==2) return !ODD && B>=2; return isprime_odd(q); }
static int allowed(uint64_t q){ return in_P(q) || is_kprime(q); }

/* ---------------- rows ---------------- */
typedef struct { int n; uint64_t *q; int *e; } fact_t;
typedef struct { uint64_t p; int nadm; int *a; fact_t *f; } row_t;
typedef struct { uint64_t o, q; int w; } pair_t;
typedef struct { uint64_t p; size_t i0,i1; uint64_t omax; pair_t *sm; size_t nsm, csm; uint64_t *W; size_t nW,cW; double lnp1; } job_t;

static void *row_worker(void *arg){
  job_t *J=arg; uint64_t p=J->p;
  size_t fo = fofs[J->i0/FCH]; for(size_t i=(J->i0/FCH)*FCH; i<J->i0; i++) fo+=fcnt[i];
  for(size_t i=J->i0;i<J->i1;i++){
    uint64_t q=pr[i]; const uint16_t *fl=flist+fo; int nf=fcnt[i]; fo+=nf;
    if(q==p) continue;
    /* factor q-1 */
    uint64_t F[16]; int k=0; uint64_t m=q-1; F[k++]=2; while(!(m&1)) m>>=1;
    for(int c=0;c<nf;c++){ F[k++]=fl[c]; while(m%fl[c]==0) m/=fl[c]; }
    if(m>1){ if(!isprime_odd(m)){ fprintf(stderr,"FATAL: factor table inconsistent at q=%llu\n",(unsigned long long)q); exit(4);} F[k++]=m; }
    uint32_t mq=(uint32_t)q, mi=m32inv(mq); uint32_t one=(uint32_t)((1ULL<<32)%q); uint32_t bm=(uint32_t)(((p%q)<<32)%q);
    uint64_t o=q-1;
    for(int c=0;c<k;c++){ uint64_t f=F[c]; while(o%f==0 && pw32(bm,o/f,one,mq,mi)==one) o/=f; }
    if(o==1) continue; /* q | p-1 : divides Phi_1 only */
    int w = pow_is_one_q2(p,o,q);
    if(o<=J->omax){ if(J->nsm==J->csm){ J->csm=J->csm?2*J->csm:1024; J->sm=realloc(J->sm,sizeof(pair_t)*J->csm);} J->sm[J->nsm++]=(pair_t){o,q,w}; }
    else {
      int bad=w;
      if(!bad){ /* EXACT: reject o iff UP(B^K * o) < DOWN((p-1)^phi(o)),  K = floor((B-1)/o) */
        uint64_t ph=o; for(int c=0;c<k;c++) if(o%F[c]==0) ph=ph/F[c]*(F[c]-1);
        xf lhs=xf_mul(xf_pow(xf_u64(B),(B-1)/o,1), xf_u64(o), 1);
        xf rhs=xf_pow(xf_u64(p-1), ph, 0);
        if(!xf_lt(lhs,rhs)) bad=1; }
      if(bad){ if(J->nW==J->cW){ J->cW=J->cW?2*J->cW:64; J->W=realloc(J->W,8*J->cW);} J->W[J->nW++]=o; }
    }
  }
  return NULL;
}
static int cmp_pair(const void*a,const void*b){ const pair_t*x=a,*y=b; if(x->o!=y->o) return x->o<y->o?-1:1; return x->q<y->q?-1:(x->q>y->q); }
static int cmp_u64(const void*a,const void*b){ uint64_t x=*(uint64_t*)a,y=*(uint64_t*)b; return x<y?-1:(x>y); }

/* Phi_d(p) exactly */
static void cyclo(mpz_t res, uint64_t p, uint64_t d){
  mpz_t num,den,t; mpz_inits(num,den,t,NULL); mpz_set_ui(num,1); mpz_set_ui(den,1);
  for(uint64_t e=1;e*e<=d;e++) if(d%e==0){ uint64_t es[2]={e,d/e}; for(int z=0;z<(e*e==d?1:2);z++){ uint64_t ee=es[z]; int mu=mobius(d/ee); if(!mu) continue;
      mpz_ui_pow_ui(t,p,ee); mpz_sub_ui(t,t,1); if(mu>0) mpz_mul(num,num,t); else mpz_mul(den,den,t);} }
  mpz_divexact(res,num,den); mpz_clears(num,den,t,NULL);
}

static size_t nrows, crows; static row_t **rows; static long rows_computed, rows_cached; static double row_time;
/* simple hash p -> row index */
static size_t hcap; static int64_t *htab;
static void hput(uint64_t p, size_t idx){ if(nrows*2>=hcap){ size_t nc=hcap?hcap*2:1024; int64_t *nt=malloc(8*nc); for(size_t i=0;i<nc;i++) nt[i]=-1; for(size_t i=0;i<hcap;i++) if(htab[i]>=0){ uint64_t pp=rows[htab[i]]->p; size_t h=(pp*0x9E3779B97F4A7C15ULL)%nc; while(nt[h]>=0) h=(h+1)%nc; nt[h]=htab[i]; } free(htab); htab=nt; hcap=nc; }
  size_t h=(p*0x9E3779B97F4A7C15ULL)%hcap; while(htab[h]>=0) h=(h+1)%hcap; htab[h]=idx; }
static row_t *hget(uint64_t p){ if(!hcap) return NULL; size_t h=(p*0x9E3779B97F4A7C15ULL)%hcap; while(htab[h]>=0){ if(rows[htab[h]]->p==p) return rows[htab[h]]; h=(h+1)%hcap; } return NULL; }
static row_t *new_row(uint64_t p){ if(nrows==crows){ crows=crows?2*crows:256; rows=realloc(rows,sizeof(row_t*)*crows);} row_t *R=calloc(1,sizeof(row_t)); R->p=p; rows[nrows]=R; nrows++; hput(p,nrows-1); return R; }

static void cache_write(row_t *R){
  if(!CACHE) return;
  fprintf(CACHE,"%llu %d",(unsigned long long)R->p,R->nadm);
  for(int i=0;i<R->nadm;i++){ fprintf(CACHE," %d:%d",R->a[i],R->f[i].n); for(int j=0;j<R->f[i].n;j++) fprintf(CACHE,",%llu^%d",(unsigned long long)R->f[i].q[j],R->f[i].e[j]); }
  fprintf(CACHE,"\n"); fflush(CACHE);
}

static row_t *compute_row(uint64_t p){
  double t0=now();
  row_t *R=new_row(p);
  double lnp1 = p>2? log((double)(p-1)) : 0.0;
  uint64_t omax;
  if(p==2) omax=B; else { double o=sqrt(6.3*(double)B*LNB/lnp1)+10; omax = o>(double)B?B:(uint64_t)o; }
  /* threads over odd prime indices 1..npr */
  job_t J[64]; pthread_t th[64]; size_t n=npr>1?npr-1:0;
  for(int t=0;t<NTH;t++){ memset(&J[t],0,sizeof(job_t)); J[t].p=p; J[t].i0=1+n*t/NTH; J[t].i1=1+n*(t+1)/NTH; J[t].omax=omax; J[t].lnp1=lnp1; pthread_create(&th[t],NULL,row_worker,&J[t]); }
  size_t nsm=0,nW=0; for(int t=0;t<NTH;t++){ pthread_join(th[t],NULL); nsm+=J[t].nsm; nW+=J[t].nW; }
  pair_t *sm=malloc(sizeof(pair_t)*(nsm+1)); uint64_t *W=malloc(8*(nW+4)); size_t a1=0,a2=0;
  for(int t=0;t<NTH;t++){ memcpy(sm+a1,J[t].sm,sizeof(pair_t)*J[t].nsm); a1+=J[t].nsm; memcpy(W+a2,J[t].W,8*J[t].nW); a2+=J[t].nW; free(J[t].sm); free(J[t].W); }
  /* exceptions (Zsigmondy) */
  if(p==2) W[a2++]=6;
  if(p>2 && ((p+1)&p)==0) W[a2++]=2;
  qsort(sm,nsm,sizeof(pair_t),cmp_pair); qsort(W,a2,8,cmp_u64);
  /* candidate list: distinct d from sm and W */
  size_t nd=0, cd=1024; uint64_t *D=malloc(8*cd);
  { size_t i=0,j=0; while(i<nsm||j<a2){ uint64_t x; if(j>=a2 || (i<nsm && sm[i].o<=W[j])) x=sm[i].o; else x=W[j];
      if(nd==0||D[nd-1]!=x){ if(nd==cd){cd*=2; D=realloc(D,8*cd);} D[nd++]=x; }
      while(i<nsm&&sm[i].o==x) i++; while(j<a2&&W[j]==x) j++; } }
  /* evaluate each candidate d */
  int ngood=0, cg=64; uint64_t *G=malloc(8*cg); fact_t *GF=malloc(sizeof(fact_t)*cg);
  mpz_t ph, t, mq; mpz_inits(ph,t,mq,NULL);
  size_t si=0;
  uint64_t *bq=malloc(8*1024); int *bw=malloc(sizeof(int)*1024); size_t cb=1024;
  for(size_t di=0;di<nd;di++){
    uint64_t d=D[di]; if(d<2) continue;
    size_t nb=0;
    if(d<=omax){ while(si<nsm && sm[si].o<d) si++; size_t s2=si; while(s2<nsm && sm[s2].o==d){ if(nb==cb){cb*=2; bq=realloc(bq,8*cb); bw=realloc(bw,sizeof(int)*cb);} bq[nb]=sm[s2].q; bw[nb]=sm[s2].w; nb++; s2++; } }
    if(d>omax || (p==2&&d==6) || (d==2 && ((p+1)&p)==0)){ /* exact bucket by scanning q = 1 mod d (step 2d if d odd) */
      if(d>omax){ nb=0; uint64_t f[16]; int kf=pfac(d,f); uint64_t step=(d&1)?2*d:d;
        for(uint64_t q=1+step; q<=B; q+=step){ if(!isprime_odd(q)||q==p) continue; if(powmod64(p,d,q)!=1) continue;
          int ok=1; for(int c=0;c<kf;c++) if(powmod64(p,d/f[c],q)==1){ok=0;break;} if(!ok) continue;
          if(nb==cb){cb*=2; bq=realloc(bq,8*cb); bw=realloc(bw,sizeof(int)*cb);} bq[nb]=q; bw[nb]=pow_is_one_q2(p,d,q); nb++; } }
    }
    uint64_t f[16]; int kf=pfac(d,f); uint64_t Pd=f[kf-1]; int Pd_ok = allowed(Pd);
    if(d>2 && p>2){ /* size filter, EXACT: reject iff UP(Pd * prod q^v) < DOWN((p-1)^phi(d)) */
      xf s = Pd_ok? xf_u64(Pd) : xf_u64(1);
      for(size_t b=0;b<nb;b++){ int v=1; if(bw[b]){ mpz_set_ui(mq,bq[b]); mpz_mul_ui(mq,mq,bq[b]); /* q^2 */
            for(v=1;;v++){ mpz_t pp; mpz_init_set_ui(pp,p); mpz_powm_ui(t,pp,d,mq); mpz_clear(pp); if(mpz_cmp_ui(t,1)!=0) break; mpz_mul_ui(mq,mq,bq[b]); } }
        s = xf_mul(s, xf_pow(xf_u64(bq[b]), (uint64_t)v, 1), 1); }
      if(xf_lt(s, xf_pow(xf_u64(p-1), phi_of(d), 0))) continue;   /* provably not smooth */
    }
    cyclo(ph,p,d);
    fact_t FF; FF.n=0; FF.q=malloc(8*(nb+2)); FF.e=malloc(sizeof(int)*(nb+2));
    for(size_t b=0;b<nb;b++){ int e=0; while(mpz_divisible_ui_p(ph,bq[b])){ mpz_divexact_ui(ph,ph,bq[b]); e++; } if(e){ FF.q[FF.n]=bq[b]; FF.e[FF.n++]=e; } }
    if(Pd_ok){ int e=0; while(mpz_divisible_ui_p(ph,Pd)){ mpz_divexact_ui(ph,ph,Pd); e++; } if(e){ FF.q[FF.n]=Pd; FF.e[FF.n++]=e; } }
    if(mpz_cmp_ui(ph,1)!=0){ free(FF.q); free(FF.e); continue; }  /* has a prime factor outside the allowed set */
    if(ngood==cg){ cg*=2; G=realloc(G,8*cg); GF=realloc(GF,sizeof(fact_t)*cg); }
    G[ngood]=d; GF[ngood]=FF; ngood++;
  }
  /* admissible exponents */
  int ca=16; R->a=malloc(sizeof(int)*ca); R->f=malloc(sizeof(fact_t)*ca);
  for(int g=0; g<ngood; g++){ uint64_t d=G[g]; int ok=1;
    { uint64_t f[16], dv[4096]; int kf=pfac(d,f), nd2=1; dv[0]=1;
      for(int c=0;c<kf && ok;c++){ int cur=nd2; uint64_t pp=1; uint64_t dd=d; int ex=0; while(dd%f[c]==0){dd/=f[c];ex++;}
        for(int x=1;x<=ex;x++){ pp*=f[c]; for(int y=0;y<cur;y++){ if(nd2>=4096){ok=0;break;} dv[nd2++]=dv[y]*pp; } } }
      if(nd2>=4096) { fprintf(stderr,"too many divisors\n"); exit(2); }
      for(int y=0;y<nd2 && ok;y++){ uint64_t e=dv[y]; if(e<2) continue; if(!bsearch(&e,G,ngood,8,cmp_u64)) ok=0; } }
    if(!ok) continue;
    /* merge factorizations of Phi_e, e | d, e > 1 */
    fact_t S; S.n=0; int cs=8; S.q=malloc(8*cs); S.e=malloc(sizeof(int)*cs);
    for(int h=0;h<ngood;h++) if(d%G[h]==0) for(int j=0;j<GF[h].n;j++){ int z; for(z=0;z<S.n;z++) if(S.q[z]==GF[h].q[j]) break;
        if(z==S.n){ if(S.n==cs){cs*=2; S.q=realloc(S.q,8*cs); S.e=realloc(S.e,sizeof(int)*cs);} S.q[z]=GF[h].q[j]; S.e[z]=0; S.n++; } S.e[z]+=GF[h].e[j]; }
    if(R->nadm==ca){ ca*=2; R->a=realloc(R->a,sizeof(int)*ca); R->f=realloc(R->f,sizeof(fact_t)*ca);} R->a[R->nadm]=(int)(d-1); R->f[R->nadm]=S; R->nadm++;
  }
  for(int g=0;g<ngood;g++){ free(GF[g].q); free(GF[g].e); } free(G); free(GF); free(D); free(sm); free(W); free(bq); free(bw);
  mpz_clears(ph,t,mq,NULL);
  rows_computed++; row_time+=now()-t0;
  cache_write(R);
  return R;
}
static row_t *get_row(uint64_t p){ row_t *R=hget(p); if(R) return R; return compute_row(p); }
static void load_cache(const char *fn){
  FILE *f=fopen(fn,"r"); if(!f) return; char *line=NULL; size_t cap=0; ssize_t len; long good_end=0;
  while((len=getline(&line,&cap,f))>0){ if(line[len-1]!='\n') break; /* partial last line */
    good_end=ftell(f);
    char *s=line; unsigned long long p; int na,off; if(sscanf(s,"%llu %d%n",&p,&na,&off)!=2) break; s+=off;
    if(hget(p)) continue; row_t *R=new_row(p); R->nadm=na; R->a=malloc(sizeof(int)*(na+1)); R->f=malloc(sizeof(fact_t)*(na+1));
    for(int i=0;i<na;i++){ int a,n; sscanf(s," %d:%d%n",&a,&n,&off); s+=off; R->a[i]=a; R->f[i].n=n; R->f[i].q=malloc(8*(n+1)); R->f[i].e=malloc(sizeof(int)*(n+1));
      for(int j=0;j<n;j++){ unsigned long long q; int e; sscanf(s,",%llu^%d%n",&q,&e,&off); s+=off; R->f[i].q[j]=q; R->f[i].e[j]=e; } }
    rows_cached++; }
  free(line); fclose(f);
  if(truncate(fn, good_end)!=0) perror("truncate");   /* drop a partially written last line (killed run) */
}

/* ---------------- DFS state (global with undo) ---------------- */
static int8_t *st;  /* per prime index: 0 free, 1 required, 2 assigned, 3 excluded */
/* small map q -> int (valuations), q -> exponent; linear-probe hash with undo log */
typedef struct { uint64_t *k; int *v; size_t cap, n; } map_t;
static map_t VAL, EXP;
static void map_init(map_t *m){ m->cap=1<<12; m->n=0; m->k=calloc(m->cap,8); m->v=calloc(m->cap,sizeof(int)); }
static int *map_slot(map_t *m, uint64_t key, int create){
  if(create && m->n*2>=m->cap){ size_t oc=m->cap; uint64_t *ok=m->k; int *ov=m->v; m->cap*=2; m->k=calloc(m->cap,8); m->v=calloc(m->cap,sizeof(int)); m->n=0;
    for(size_t i=0;i<oc;i++) if(ok[i]){ size_t h=(ok[i]*0x9E3779B97F4A7C15ULL)&(m->cap-1); while(m->k[h]) h=(h+1)&(m->cap-1); m->k[h]=ok[i]; m->v[h]=ov[i]; m->n++; } free(ok); free(ov); }
  size_t h=(key*0x9E3779B97F4A7C15ULL)&(m->cap-1); while(m->k[h]){ if(m->k[h]==key) return &m->v[h]; h=(h+1)&(m->cap-1); }
  if(!create) return NULL; m->k[h]=key; m->v[h]=0; m->n++; return &m->v[h]; }
static int mget(map_t *m, uint64_t key){ int *s=map_slot(m,key,0); return s?*s:0; }
static int getst(uint64_t q){ long i=pidx(q); return i<0? -1 : st[i]; }
static void setst(uint64_t q,int v){ long i=pidx(q); st[i]=v; }

static uint64_t *REQ; static size_t nreq, creq;   /* required list (unordered) */
static mpz_t MN; /* M_up = MN / 2^64 */
static long long NODES; static long long NSOL; static mpz_t SOLS[1024];
static long long node_limit;

static void logf_(const char *fmt, ...);
#include <stdarg.h>
static void logf_(const char *fmt, ...){ if(!LOG) return; va_list ap; va_start(ap,fmt); vfprintf(LOG,fmt,ap); va_end(ap); }

static double last_report;
static void report(int depth){ double t=now(); if(t-last_report>30){ last_report=t; fprintf(stderr,"[%.0fs] nodes=%lld rows=%ld(+%ld cached) rowtime=%.0fs depth=%d\n",t-T0,NODES,rows_computed,rows_cached,row_time,depth); fflush(stderr);} }

/* A = an/ad (exact), E = en/ed : product over assigned+excluded of p/(p-1) */
static void dfs(int depth, mpz_t an, mpz_t ad, mpz_t en, mpz_t ed){
  NODES++; if(node_limit && NODES>node_limit){ fprintf(stderr,"node limit\n"); exit(3);} report(depth);
  mpz_t L,Rr,t; mpz_inits(L,Rr,t,NULL);
  /* lower bound */
  if(nreq){ mpz_set(L,an); mpz_set(Rr,ad); for(size_t i=0;i<nreq;i++){ mpz_mul_ui(L,L,REQ[i]+1); mpz_mul_ui(Rr,Rr,REQ[i]); }
    mpz_mul_si(L,L,KD); mpz_mul_si(Rr,Rr,KN); if(mpz_cmp(L,Rr)>0){ logf_("%d LB\n",depth); goto out; } }
  else { mpz_mul_si(L,an,KD); mpz_mul_si(Rr,ad,KN); if(mpz_cmp(L,Rr)>0){ logf_("%d LB\n",depth); goto out; } }
  /* upper bound: prune iff A < k and A * M_up / E < k  <=>  an*MN*ed*KD < KN*ad*en*2^64 */
  mpz_mul_si(L,an,KD); mpz_mul_si(Rr,ad,KN);
  if(mpz_cmp(L,Rr)<0){ mpz_mul(L,an,MN); mpz_mul(L,L,ed); mpz_mul_si(L,L,KD); mpz_mul(Rr,ad,en); mpz_mul_si(Rr,Rr,KN); mpz_mul_2exp(Rr,Rr,64);
    if(mpz_cmp(L,Rr)<0){ logf_("%d UB\n",depth); goto out; } }
  if(nreq){
    size_t ri=0; for(size_t i=1;i<nreq;i++) if(REQ[i]>REQ[ri]) ri=i;
    uint64_t r=REQ[ri];
    row_t *R=get_row(r);
    int need=mget(&VAL,r)-kval(r);
    /* remove r from REQ (swap with last), restore later */
    REQ[ri]=REQ[nreq-1]; nreq--;
    for(int ia=0; ia<R->nadm; ia++){
      int a=R->a[ia]; fact_t *f=&R->f[ia];
      if(a<need) continue;
      if(ODD && r!=2 && (a&1)){ int v2=mget(&VAL,2); if(v2+1>kval(2)) continue; } /* sigma(r^a) even; sound prefilter */
      /* check factors */
      int ok=1; for(int j=0;j<f->n;j++) if(f->q[j]==r){ok=0;break;}
      if(!ok){ logf_("%d R %llu %d self\n",depth,(unsigned long long)r,a); continue; }
      size_t req0=nreq; int failq=0;
      for(int j=0;j<f->n && ok;j++){ uint64_t q=f->q[j]; int e=f->e[j]; int nv=mget(&VAL,q)+e; int s=in_P(q)?getst(q):-1;
        if(s==3){ if(nv>kval(q)){ok=0;failq=1;} }
        else if(s==2){ if(nv>mget(&EXP,q)+kval(q)){ok=0;failq=2;} }
        else if(in_P(q) && !is_kprime(q)){ if(s==0){ /* becomes required (applied below) */ } }
        else if(in_P(q)){ }
        else { if(nv>kval(q)){ok=0;failq=3;} }
        if(!ok) logf_("%d R %llu %d q%llu c%d\n",depth,(unsigned long long)r,a,(unsigned long long)q,failq); }
      if(!ok) continue;
      { int vr=mget(&VAL,r); for(int j=0;j<f->n;j++) if(f->q[j]==r) vr+=f->e[j]; if(vr>a+kval(r)){ logf_("%d R %llu %d selfval\n",depth,(unsigned long long)r,a); continue; } }
      /* apply */
      for(int j=0;j<f->n;j++){ uint64_t q=f->q[j]; *map_slot(&VAL,q,1)+=f->e[j];
        if(in_P(q) && !is_kprime(q) && getst(q)==0){ setst(q,1); if(nreq==creq){creq=creq?2*creq:256; REQ=realloc(REQ,8*creq);} REQ[nreq++]=q; } }
      setst(r,2); *map_slot(&EXP,r,1)=a;
      mpz_t nan,nad,nen,ned; mpz_inits(nan,nad,nen,ned,NULL);
      /* sigma(r^a) from factorization */
      mpz_set_ui(t,1); for(int j=0;j<f->n;j++){ mpz_ui_pow_ui(L,f->q[j],f->e[j]); mpz_mul(t,t,L); }
      mpz_mul(nan,an,t); mpz_ui_pow_ui(L,r,a); mpz_mul(nad,ad,L); mpz_gcd(L,nan,nad); mpz_divexact(nan,nan,L); mpz_divexact(nad,nad,L);
      mpz_mul_ui(nen,en,r); mpz_mul_ui(ned,ed,r-1);
      logf_("%d A %llu %d\n",depth,(unsigned long long)r,a);
      dfs(depth+1,nan,nad,nen,ned);
      mpz_clears(nan,nad,nen,ned,NULL);
      /* undo */
      *map_slot(&EXP,r,1)=0; setst(r,1);
      while(nreq>req0){ setst(REQ[nreq-1],0); nreq--; }
      for(int j=0;j<f->n;j++) *map_slot(&VAL,f->q[j],1)-=f->e[j];
    }
    /* restore r into REQ */
    if(nreq==creq){creq=creq?2*creq:256; REQ=realloc(REQ,8*creq);} REQ[nreq++]=REQ[ri]; REQ[ri]=r;
    goto out;
  }
  /* required empty: forced k-primes */
  { uint64_t forced[32]; int nf=0;
    for(int i=0;i<nkv;i++){ uint64_t q=kvp[i]; if(in_P(q) && getst(q)==0 && mget(&VAL,q)>kvv[i]) forced[nf++]=q; }
    if(nf){ for(int i=0;i<nf;i++){ setst(forced[i],1); if(nreq==creq){creq=creq?2*creq:256; REQ=realloc(REQ,8*creq);} REQ[nreq++]=forced[i]; }
      logf_("%d F\n",depth); dfs(depth+1,an,ad,en,ed);
      for(int i=0;i<nf;i++){ setst(forced[i],0); } nreq-=nf; goto out; } }
  mpz_mul_si(L,an,KD); mpz_mul_si(Rr,ad,KN);
  if(mpz_cmp(L,Rr)==0){
    int good=1, nas=0; mpz_set_ui(t,1);
    for(size_t i=0;i<VAL.cap;i++) if(VAL.k[i] && VAL.v[i]){ uint64_t q=VAL.k[i]; int ex = (in_P(q)&&getst(q)==2)? mget(&EXP,q):0; if(VAL.v[i]!=ex+kval(q)) good=0; }
    for(size_t i=0;i<EXP.cap;i++) if(EXP.k[i] && EXP.v[i]){ uint64_t q=EXP.k[i]; nas++; if(mget(&VAL,q)!=EXP.v[i]+kval(q)) good=0; mpz_ui_pow_ui(L,q,EXP.v[i]); mpz_mul(t,t,L); }
    for(int i=0;i<nkv;i++){ uint64_t q=kvp[i]; if(!(in_P(q)&&getst(q)==2) && mget(&VAL,q)!=kvv[i]) good=0; }
    if(good && nas){ if(NSOL<1024){ mpz_init_set(SOLS[NSOL],t);} NSOL++; logf_("%d SOL ",depth); if(LOG) mpz_out_str(LOG,10,t); logf_("\n"); }
    else logf_("%d EQ\n",depth);
    goto out; }
  if(mpz_cmp(L,Rr)>0){ logf_("%d OVER\n",depth); goto out; }
  { size_t i; for(i=(ODD?1:0); i<npr; i++) if(st[i]==0) break;
    if(i>=npr){ logf_("%d NOFREE\n",depth); goto out; }
    uint64_t p=pr[i];
    /* include */
    st[i]=1; if(nreq==creq){creq=creq?2*creq:256; REQ=realloc(REQ,8*creq);} REQ[nreq++]=p;
    logf_("%d I %llu\n",depth,(unsigned long long)p);
    dfs(depth+1,an,ad,en,ed);
    nreq--; st[i]=0;
    /* exclude */
    st[i]=3; mpz_t nen,ned; mpz_inits(nen,ned,NULL); mpz_mul_ui(nen,en,p); mpz_mul_ui(ned,ed,p-1);
    logf_("%d X %llu\n",depth,(unsigned long long)p);
    dfs(depth+1,an,ad,nen,ned);
    mpz_clears(nen,ned,NULL); st[i]=0; }
out:
  mpz_clears(L,Rr,t,NULL);
}

/* rigorous rational upper bound for prod_{p in P} p/(p-1):  MN/2^64 */
static void compute_Mup(void){
  u128 T=0; /* fixed point 2^100 */
  u128 one100=((u128)1)<<100;
  for(size_t i=0;i<npr;i++){ uint64_t p=pr[i]; if(p==2){ if(ODD) continue;
      /* log 2 <= 0.6931471805599453095 */ mpz_t z; mpz_init(z); mpz_set_str(z,"6931471805599453095",10); mpz_mul_2exp(z,z,100); mpz_cdiv_q_ui(z,z,1000000000ULL); mpz_cdiv_q_ui(z,z,10000000000ULL);
      u128 v=0; size_t cnt; uint64_t w[2]={0,0}; mpz_export(w,&cnt,-1,8,0,0,z); v=((u128)w[1]<<64)|w[0]; T+=v; mpz_clear(z); continue; }
    /* -log(1-x) = sum_{j>=1} x^j/j, x=1/p<=1/3: exact terms (rounded up) while p^j <= 2^100, then the tail
       sum_{j>=J} x^j/j <= x^J/(J(1-x)) <= 1.5*2^-100  -> +2 units */
    u128 pk=p; for(uint64_t j=1; pk<=one100; j++){ u128 den=pk*(u128)j; T+=(one100+den-1)/den; if(pk>one100/p) break; pk*=p; }
    T+=2; }
  /* y = T/2^100 ; exp(y) <= sum_{k<=K} y^k/k! + y^{K+1}/(K+1)! * 1/(1-y/(K+2)) */
  mpq_t y,term,sum,tmp; mpq_inits(y,term,sum,tmp,NULL);
  mpz_t Tz; mpz_init(Tz); uint64_t w[2]={(uint64_t)T,(uint64_t)(T>>64)}; mpz_import(Tz,2,-1,8,0,0,w);
  mpq_set_z(y,Tz); mpz_t two100; mpz_init(two100); mpz_ui_pow_ui(two100,2,100); mpq_set_den(tmp,two100); mpq_set_num(tmp,Tz); mpq_canonicalize(tmp); mpq_set(y,tmp);
  mpq_set_ui(term,1,1); mpq_set_ui(sum,1,1); int K=120;
  for(int k=1;k<=K;k++){ mpq_mul(term,term,y); mpq_set_ui(tmp,1,k); mpq_mul(term,term,tmp); mpq_add(sum,sum,term); }
  mpq_mul(term,term,y); mpq_set_ui(tmp,1,K+1); mpq_mul(term,term,tmp); /* y^{K+1}/(K+1)! */
  mpq_set_ui(tmp,K+2,1); mpq_sub(tmp,tmp,y); mpq_div(tmp,tmp,y); /* (K+2-y)/y ... want 1/(1-y/(K+2)) = (K+2)/(K+2-y) */
  mpq_set_ui(tmp,K+2,1); { mpq_t d; mpq_init(d); mpq_set_ui(d,K+2,1); mpq_sub(d,d,y); mpq_div(tmp,tmp,d); mpq_clear(d); }
  mpq_mul(term,term,tmp); mpq_add(sum,sum,term);
  /* MN = ceil(sum * 2^64) */
  mpz_init(MN); mpz_t nu; mpz_init(nu); mpz_mul_2exp(nu,mpq_numref(sum),64); mpz_cdiv_q(MN,nu,mpq_denref(sum));
  fprintf(stderr,"M_up = %.12f (log %.12f)\n", mpz_get_d(MN)/18446744073709551616.0, mpq_get_d(y));
  mpq_clears(y,term,sum,tmp,NULL); mpz_clears(Tz,two100,nu,NULL);
}

int main(int argc,char**argv){
  if(argc<7){ fprintf(stderr,"usage: lpf B kn/kd odd|even threads rowcache logfile [node_limit]\n"); return 1; }
  B=strtoull(argv[1],0,10); if(sscanf(argv[2],"%ld/%ld",&KN,&KD)<1) return 1; if(!strchr(argv[2],'/')) KD=1;
  ODD=!strcmp(argv[3],"odd"); NTH=atoi(argv[4]); if(NTH<1) NTH=1; if(NTH>64) NTH=64;
  if(argc>7) node_limit=atoll(argv[7]);
  T0=now(); LNB=log((double)B);
  build_tables(); fprintf(stderr,"tables: %zu primes <= %llu built in %.1fs\n",npr,(unsigned long long)B,now()-T0);
  /* kval */
  { long a=KN,b=KD; long g; { long x=a,y=b; while(y){long r=x%y;x=y;y=r;} g=x; } a/=g; b/=g; KN=a; KD=b;
    for(long q=2;q<=1000000;q++){ int c=0; while(a%q==0){a/=q;c++;} while(b%q==0){b/=q;c--;} if(c){ kvp[nkv]=q; kvv[nkv]=c; nkv++; } if(a==1&&b==1) break; }
    for(int i=0;i<nkv;i++) if(kvp[i]>B){ fprintf(stderr,"k has a prime factor > B; unsupported\n"); return 1; } }
  compute_Mup();
  st=calloc(npr,1); map_init(&VAL); map_init(&EXP);
  load_cache(argv[5]); CACHE=fopen(argv[5],"a");
  LOG = strcmp(argv[6],"-")? fopen(argv[6],"w") : NULL;
  if(LOG) fprintf(LOG,"# lpf B=%llu k=%ld/%ld mode=%s\n",(unsigned long long)B,KN,KD,ODD?"odd":"even");
  mpz_t an,ad,en,ed; mpz_inits(an,ad,en,ed,NULL); mpz_set_ui(an,1); mpz_set_ui(ad,1); mpz_set_ui(en,1); mpz_set_ui(ed,1);
  /* denominator primes of k are required from the start */
  for(int i=0;i<nkv;i++) if(kvv[i]<0){ if(!in_P(kvp[i])){ fprintf(stderr,"denominator prime not allowed: no solutions\n"); printf("RESULT nodes=0 solutions=0\n"); return 0; }
      setst(kvp[i],1); if(nreq==creq){creq=creq?2*creq:256; REQ=realloc(REQ,8*creq);} REQ[nreq++]=kvp[i]; }
  last_report=now();
  dfs(0,an,ad,en,ed);
  if(LOG){ fprintf(LOG,"# END nodes=%lld solutions=%lld\n",NODES,NSOL); fclose(LOG); }
  printf("RESULT B=%llu k=%ld/%ld mode=%s nodes=%lld rows_computed=%ld rows_cached=%ld rowtime=%.1fs total=%.1fs solutions=%lld\n",
    (unsigned long long)B,KN,KD,ODD?"odd":"even",NODES,rows_computed,rows_cached,row_time,now()-T0,NSOL);
  for(long long i=0;i<NSOL && i<1024;i++){ printf("SOL "); mpz_out_str(stdout,10,SOLS[i]); printf("\n"); }
  return 0;
}
