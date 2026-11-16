/*
 * rowverify.c -- FULL (not sampled) independent verification of the rows file of lpf.c.
 *
 * Claim to verify for every row prime p:  the list of admissible exponents a (sigma(p^a) factors over the
 * allowed primes {2} u {odd primes <= B}) is COMPLETE and each listed factorization is the right one.
 *
 * Independent of lpf.c: own prime source (primesieve library), own factorisation of q-1 (trial division), own
 * order algorithm (bottom-up per prime power, plain 64-bit '%' arithmetic), own Wieferich test (own 64-bit
 * Montgomery mod q^2, unit-tested against GMP), own rigorous size bounds (integer fixed-point log2 with
 * directed rounding + integer "xf" floats), own cyclotomic evaluation (Phi_{l m}(x) = Phi_m(x^l)/Phi_m(x)).
 *
 * Mathematics.  For d >= 2 let O_p(d) = { odd primes q <= B, q != p : ord_q(p) = d } (the bucket).
 *  (1) a prime q | Phi_d(p) has ord_q(p) = d, or q = P(d) (largest prime of d) and then v_q = 1 for d > 2.
 *  (2) Bang-Zsigmondy: Phi_d(p) has a prime of order d unless d = 2 and p+1 = 2^k (p odd).
 *  So Phi_d(p) is allowed-smooth only if d = ord_q(p) for some odd q <= B, or (d = 2, p+1 = 2^k), and then
 *      Phi_d(p) = prod_{q in O_p(d)} q^{v_q} * P(d)^{0 or more}.
 *  Bound for a single order o: |O_p(o)| <= K = floor((B-1)/o) (all are = 1 mod o, <= B); if none of them is
 *  Wieferich-type (p^o = 1 mod q^2) then v_q = 1 and the smooth part is <= B^K * o.  If
 *      K*log2(B) + log2(o) < phi(o)*log2(p-1)       (evaluated with rigorous integer bounds)
 *  then Phi_o(p) > (p-1)^phi(o) > smooth part: o is NOT good.  Such o are "dropped"; all others are "kept".
 *  Whether o is kept depends only on (p,o), so for a kept o every q of that order is stored: its bucket is
 *  complete.  If a dropped o has a Wieferich-type q, o is re-examined with an exact bucket built by scanning
 *  the progression q = 1 (mod o).
 *  For each kept o: exact v_q (GMP), rigorous size test  UP(P(o) prod q^v) < DOWN((p-1)^phi(o)) => not good,
 *  otherwise Phi_o(p) is computed exactly and divided by its bucket primes and P(o): good iff quotient 1.
 *  Admissible a <=> every e | a+1, e > 1, is good; the factorization of sigma(p^a) is the sum over e.
 *
 * usage: rowverify B rowsfile threads [first_row last_row]   (rows are numbered 0.. in file order)
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <pthread.h>
#include <time.h>
#include <gmp.h>
#include <primesieve.h>

typedef unsigned __int128 u128;
static uint64_t B; static int NTH;
static double now(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec; }

/* ---------- prime data from primesieve ---------- */
static uint8_t *obit;                       /* bit (n>>1) set <=> n odd prime <= B */
static inline int oprime(uint64_t n){ return n<=B && (n&1) && ((obit[n>>4]>>((n>>1)&7))&1); }
static uint32_t *SP; static size_t nSP;     /* odd primes <= sqrt(B) for trial division */
static uint32_t *QL; static size_t nQ;      /* all odd primes <= B */

/* ---------- integer fixed-point log2 with directed rounding (F = 32 fractional bits) ----------
   lg2_bound(x, up): returns L with L <= 2^32*log2(x) (up=0) or L >= 2^32*log2(x) (up=1).  Repeated squaring of
   a 62-bit fixed-point mantissa in [1,2); every rounding goes in the stated direction (see review notes). */
static uint64_t lg2_bound(uint64_t x, int up){
  int k=63-__builtin_clzll(x); uint64_t ONE=1ULL<<62;
  u128 y = ((u128)x<<62)>>k;          /* exact: x/2^k * 2^62, since x < 2^(k+1) and k <= 63 */
  uint64_t L=(uint64_t)k<<32;
  for(int i=31;i>=0;i--){
    u128 sq=y*y; u128 ny=sq>>62; if(up && (sq & ((((u128)1)<<62)-1))) ny++;
    if(ny >= ((u128)2*ONE)){ L |= 1ULL<<i; u128 h=ny>>1; if(up && (ny&1)) h++; ny=h; }
    y=ny; }
  if(up) L+=1;                        /* remaining fraction < 2^-32 */
  return L; }

/* ---------- xf: integer floats m*2^e, m in [2^63,2^64), directed rounding ---------- */
typedef struct { uint64_t m; int64_t e; } xf;
static inline xf xf_u64(uint64_t x){ xf r; int s=__builtin_clzll(x); r.m=x<<s; r.e=-(int64_t)s; return r; }
static inline xf xf_mul(xf a, xf b, int up){ xf r; u128 P=(u128)a.m*b.m; int sh=(P>>127)?64:63;
  uint64_t m=(uint64_t)(P>>sh); u128 rem=P&((((u128)1)<<sh)-1); r.e=a.e+b.e+sh;
  if(up&&rem){ m++; if(m==0){ m=1ULL<<63; r.e++; } } r.m=m; return r; }
static inline xf xf_pow(xf x, uint64_t n, int up){ xf r=xf_u64(1); while(n){ if(n&1) r=xf_mul(r,x,up); n>>=1; if(n) x=xf_mul(x,x,up);} return r; }
static inline int xf_lt(xf a, xf b){ if(a.e!=b.e) return a.e<b.e; return a.m<b.m; }

/* ---------- modular arithmetic ---------- */
static inline uint64_t pm(uint64_t b, uint64_t e, uint64_t q){ uint64_t r=1; b%=q; while(e){ if(e&1) r=r*b%q; e>>=1; if(e) b=b*b%q; } return r; } /* q < 2^32 */
/* Montgomery mod M = q^2 < 2^62 */
typedef struct { uint64_t M, Mi, R1, R2; } mont_t;
static inline uint64_t redc(u128 T, const mont_t *c){ uint64_t mlo=(uint64_t)T*c->Mi; u128 t=(T+(u128)mlo*c->M)>>64; uint64_t r=(uint64_t)t; return r>=c->M? r-c->M : r; }
static void mont_init(mont_t *c, uint64_t M){ c->M=M; uint64_t inv=1; for(int i=0;i<7;i++) inv*=2-M*inv; c->Mi=(uint64_t)(0-inv);   /* -M^-1 mod 2^64 */
  c->R1=(uint64_t)((((u128)1)<<64)%M); c->R2=(uint64_t)(((u128)c->R1*c->R1)%M); }
static inline int pow_is_one_mod(uint64_t b, uint64_t e, const mont_t *c){
  uint64_t x=redc((u128)(b%c->M)*c->R2,c), r=c->R1; while(e){ if(e&1) r=redc((u128)r*x,c); e>>=1; if(e) x=redc((u128)x*x,c); } return r==c->R1; }

/* ---------- rows file ---------- */
typedef struct { int a; int n; uint64_t *q; int *e; } claim_t;
typedef struct { uint64_t p; int nadm; claim_t *c; uint64_t lp_dn; } crow_t;
static crow_t *RW; static size_t nRW;
static void read_rows(const char *fn){
  FILE *f=fopen(fn,"r"); if(!f){ perror(fn); exit(1);} char *line=NULL; size_t cap=0; ssize_t len; size_t c=0;
  while((len=getline(&line,&cap,f))>0){ if(line[len-1]!='\n') break;
    if(nRW==c){ c=c?2*c:1024; RW=realloc(RW,sizeof(crow_t)*c); }
    crow_t *R=&RW[nRW++]; char *s=line; int off; unsigned long long p; sscanf(s,"%llu %d%n",&p,&R->nadm,&off); s+=off; R->p=p;
    R->c=malloc(sizeof(claim_t)*(R->nadm+1));
    for(int i=0;i<R->nadm;i++){ claim_t *C=&R->c[i]; sscanf(s," %d:%d%n",&C->a,&C->n,&off); s+=off; C->q=malloc(8*(C->n+1)); C->e=malloc(sizeof(int)*(C->n+1));
      for(int j=0;j<C->n;j++){ unsigned long long q; sscanf(s,",%llu^%d%n",&q,&C->e[j],&off); s+=off; C->q[j]=q; } } }
  free(line); fclose(f); }

/* ---------- streaming phase ---------- */
typedef struct { uint32_t o, qw; } ent_t;           /* qw = q | (w << 31)  (q < 2^31) */
typedef struct { ent_t *v; size_t n, c; uint64_t *sc; size_t ns, cs; } store_t;
static size_t R0, R1;                                /* rows [R0, R1) in this run */
static uint64_t LB_up;                               /* >= 2^32 log2 B */
typedef struct { size_t q0, q1; store_t *S; long long pairs; } tjob_t;

static void *stream_worker(void *arg){
  tjob_t *J=arg; size_t np=R1-R0;
  for(size_t qi=J->q0; qi<J->q1; qi++){
    uint64_t q=QL[qi], n=q-1; uint64_t f[12]; int e[12], k=0;
    { uint64_t m=n; int s=__builtin_ctzll(m); m>>=s; f[k]=2; e[k]=s; k++;
      for(size_t i=0;i<nSP;i++){ uint64_t l=SP[i]; if(l*l>m) break; if(m%l==0){ int c=0; while(m%l==0){ m/=l; c++; } f[k]=l; e[k]=c; k++; } }
      if(m>1){ f[k]=m; e[k]=1; k++; } }
    uint64_t cof[12]; for(int i=0;i<k;i++){ uint64_t pe=1; for(int j=0;j<e[i];j++) pe*=f[i]; cof[i]=n/pe; }
    mont_t mc; mont_init(&mc, q*q);
    for(size_t r=0;r<np;r++){
      uint64_t p=RW[R0+r].p; if(p==q) continue;
      uint64_t o=1, ph=1;
      for(int i=0;i<k;i++){ uint64_t y=pm(p,cof[i],q); int j=0; while(y!=1){ y=pm(y,f[i],q); j++; }
        if(j){ uint64_t t=f[i]-1; o*=f[i]; for(int z=1;z<j;z++){ o*=f[i]; t*=f[i]; } ph*=t; } }
      if(o==1) continue;                                   /* q | p-1 */
      J->pairs++;
      /* keep o unless  K*log2 B + log2 o < phi(o)*log2(p-1)  (rigorous: LB_up, bitlen(o), lp_dn) */
      uint64_t K=(B-1)/o; int bl=64-__builtin_clzll(o);
      u128 lhs=(u128)K*LB_up + ((u128)bl<<32), rhs=(u128)ph*RW[R0+r].lp_dn;
      store_t *S=&J->S[r];
      if(!(lhs<rhs)){ if(S->n==S->c){ S->c=S->c?2*S->c:4096; S->v=realloc(S->v,sizeof(ent_t)*S->c);} S->v[S->n++]=(ent_t){(uint32_t)o,(uint32_t)q}; }
      else if(pow_is_one_mod(p,o,&mc)){ if(S->ns==S->cs){ S->cs=S->cs?2*S->cs:16; S->sc=realloc(S->sc,8*S->cs);} S->sc[S->ns++]=o; }
    }
  }
  return NULL; }

static int cmp_ent(const void *a,const void *b){ const ent_t *x=a,*y=b; if(x->o!=y->o) return x->o<y->o?-1:1; return (x->qw&0x7fffffff)<(y->qw&0x7fffffff)?-1:1; }
static int cmp_u64(const void *a,const void *b){ uint64_t x=*(const uint64_t*)a,y=*(const uint64_t*)b; return x<y?-1:(x>y); }

static int pfac(uint64_t n, uint64_t *f){ int k=0; for(uint64_t d=2; d*d<=n; d++) if(n%d==0){ f[k++]=d; while(n%d==0) n/=d; } if(n>1) f[k++]=n; return k; }

/* Phi_o(p) by Phi_{m l}(x) = Phi_m(x^l)/Phi_m(x) (l prime, l not | m) and Phi_o(x) = Phi_rad(o)(x^(o/rad)) */
static void cyc_rec(mpz_t res, const uint64_t *L, int k, const mpz_t x){
  if(k==0){ mpz_sub_ui(res,x,1); return; }
  mpz_t xl,a,b; mpz_inits(xl,a,b,NULL); mpz_pow_ui(xl,x,L[k-1]);
  cyc_rec(a,L,k-1,xl); cyc_rec(b,L,k-1,x);
  if(!mpz_divisible_p(a,b)){ fprintf(stderr,"FATAL: cyclotomic recursion not exact\n"); exit(5); }
  mpz_divexact(res,a,b); mpz_clears(xl,a,b,NULL); }
static void cyclo2(mpz_t res, uint64_t p, uint64_t o){
  uint64_t L[16]; int k=pfac(o,L); uint64_t rad=1; for(int i=0;i<k;i++) rad*=L[i];
  mpz_t x; mpz_init(x); mpz_ui_pow_ui(x,p,o/rad); cyc_rec(res,L,k,x); mpz_clear(x); }

typedef struct { uint64_t d; int n; uint64_t q[64]; int e[64]; } good_t;

static int verify_row(crow_t *R, ent_t *E, size_t nE, uint64_t *SC, size_t nS, FILE *out){
  uint64_t p=R->p; double t0=now();
  qsort(E,nE,sizeof(ent_t),cmp_ent); qsort(SC,nS,8,cmp_u64);
  /* candidate orders: kept orders, scan orders, exception d=2 if p+1 = 2^k */
  size_t nd=0; uint64_t *D=malloc(8*(nE+nS+2));
  for(size_t i=0;i<nE;i++) if(!nd || D[nd-1]!=E[i].o) D[nd++]=E[i].o;
  for(size_t i=0;i<nS;i++) D[nd++]=SC[i];
  if(((p+1)&p)==0) D[nd++]=2;
  qsort(D,nd,8,cmp_u64); { size_t w=0; for(size_t i=0;i<nd;i++) if(!w||D[w-1]!=D[i]) D[w++]=D[i]; nd=w; }
  good_t *G=malloc(sizeof(good_t)*(nd+1)); size_t ng=0; long ncand=0, nexact=0;
  mpz_t ph,mq,t,pz; mpz_inits(ph,mq,t,pz,NULL); mpz_set_ui(pz,p);
  size_t ei=0; uint64_t *bq=NULL; size_t cb=0;
  for(size_t di=0; di<nd; di++){
    uint64_t d=D[di]; size_t nb=0;
    while(ei<nE && E[ei].o<d) ei++;
    int scan = bsearch(&d,SC,nS,8,cmp_u64)!=NULL;
    if(scan){ /* exact bucket by progression scan */
      uint64_t ff[16]; int kf=pfac(d,ff); uint64_t step=(d&1)?2*d:d;
      for(uint64_t q=1+step;q<=B;q+=step){ if(!oprime(q)||q==p) continue; if(pm(p,d,q)!=1) continue;
        int ok=1; for(int c=0;c<kf;c++) if(pm(p,d/ff[c],q)==1){ ok=0; break; } if(!ok) continue;
        if(nb==cb){ cb=cb?2*cb:1024; bq=realloc(bq,8*cb);} bq[nb++]=q; }
      for(size_t j=ei;j<nE && E[j].o==d;j++){ /* consistency: kept entries of a scan order (cannot happen) */
        fprintf(out,"WARN p=%llu order %llu both kept and scanned\n",(unsigned long long)p,(unsigned long long)d); break; }
    } else {
      for(size_t j=ei;j<nE && E[j].o==d;j++){ if(nb==cb){ cb=cb?2*cb:1024; bq=realloc(bq,8*cb);} bq[nb++]=E[j].qw & 0x7fffffff; }
    }
    uint64_t ff[16]; int kf=pfac(d,ff); uint64_t Pd=ff[kf-1]; int Pd_ok = (Pd==2) || oprime(Pd);
    uint64_t phd=d; for(int c=0;c<kf;c++) phd=phd/ff[c]*(ff[c]-1);
    ncand++;
    if(d>2){ /* rigorous size test with exact valuations */
      xf s=xf_u64(Pd);
      for(size_t b=0;b<nb;b++){ uint64_t q=bq[b]; int v=1; mpz_set_ui(mq,q); mpz_mul_ui(mq,mq,q);
        for(;;){ mpz_powm_ui(t,pz,d,mq); if(mpz_cmp_ui(t,1)!=0) break; v++; mpz_mul_ui(mq,mq,q); }
        s=xf_mul(s, xf_pow(xf_u64(q),(uint64_t)v,1), 1); }
      if(xf_lt(s, xf_pow(xf_u64(p-1),phd,0))) continue;
    }
    nexact++;
    cyclo2(ph,p,d);
    good_t g; g.d=d; g.n=0; int over=0;
    for(size_t b=0;b<nb;b++){ int c=0; while(mpz_divisible_ui_p(ph,bq[b])){ mpz_divexact_ui(ph,ph,bq[b]); c++; } if(c){ if(g.n>=64){over=1;break;} g.q[g.n]=bq[b]; g.e[g.n++]=c; } }
    if(Pd_ok){ int c=0; while(mpz_divisible_ui_p(ph,Pd)){ mpz_divexact_ui(ph,ph,Pd); c++; } if(c){ if(g.n>=64) over=1; else { g.q[g.n]=Pd; g.e[g.n++]=c; } } }
    if(over){ fprintf(out,"FATAL p=%llu d=%llu too many factors\n",(unsigned long long)p,(unsigned long long)d); exit(6); }
    if(mpz_cmp_ui(ph,1)==0) G[ng++]=g;
  }
  /* admissible exponents and comparison with the claim */
  int mism=0, nadm=0;
  for(size_t gi=0; gi<ng; gi++){ uint64_t d=G[gi].d; int ok=1;
    uint64_t acc_q[256]; int acc_e[256], na=0;
    for(uint64_t e=2;e<=d && ok;e++) if(d%e==0){ size_t h; for(h=0;h<ng;h++) if(G[h].d==e) break; if(h==ng){ ok=0; break; }
        for(int j=0;j<G[h].n;j++){ int z; for(z=0;z<na;z++) if(acc_q[z]==G[h].q[j]) break; if(z==na){ acc_q[na]=G[h].q[j]; acc_e[na]=0; na++; } acc_e[z]+=G[h].e[j]; } }
    if(!ok) continue;
    nadm++;
    int a=(int)(d-1), found=-1; for(int i=0;i<R->nadm;i++) if(R->c[i].a==a){ found=i; break; }
    if(found<0){ mism++; fprintf(out,"MISMATCH p=%llu: exponent a=%d admissible but MISSING in rows file\n",(unsigned long long)p,a); continue; }
    claim_t *C=&R->c[found]; int same=(C->n==na);
    for(int j=0;j<C->n && same;j++){ int z; for(z=0;z<na;z++) if(acc_q[z]==C->q[j]) break; if(z==na || acc_e[z]!=C->e[j]) same=0; }
    if(!same){ mism++; fprintf(out,"MISMATCH p=%llu a=%d: factorization differs\n",(unsigned long long)p,a); }
  }
  if(nadm!=R->nadm){ mism++; fprintf(out,"MISMATCH p=%llu: %d admissible found, rows file lists %d\n",(unsigned long long)p,nadm,R->nadm); }
  fprintf(out,"ROW p=%llu ok=%d adm=%d kept=%zu scan=%zu cand=%ld exact=%ld good=%zu %.2fs\n",(unsigned long long)p,!mism,nadm,nE,nS,ncand,nexact,ng,now()-t0);
  fflush(out);
  mpz_clears(ph,mq,t,pz,NULL); free(D); free(G); free(bq);
  return mism; }

int main(int argc,char**argv){
  if(argc<4){ fprintf(stderr,"usage: rowverify B rowsfile threads [first last]\n"); return 1; }
  B=strtoull(argv[1],0,10); NTH=atoi(argv[3]); if(NTH<1) NTH=1;
  if(B>=(1ULL<<31)){ fprintf(stderr,"B must be < 2^31\n"); return 1; }
  double T0=now();
  read_rows(argv[2]);
  R0=0; R1=nRW; if(argc>5){ R0=strtoull(argv[4],0,10); R1=strtoull(argv[5],0,10)+1; if(R1>nRW) R1=nRW; }
  /* primes */
  { primesieve_iterator it; primesieve_init(&it); uint64_t q; size_t cQ=1<<20; QL=malloc(4*cQ); obit=calloc((B>>4)+2,1);
    uint64_t r=1; while((r+1)*(r+1)<=B) r++; SP=malloc(4*(r+2)); nSP=0;
    while((q=primesieve_next_prime(&it))<=B){ if(q==2) continue; if(nQ==cQ){ cQ*=2; QL=realloc(QL,4*cQ);} QL[nQ++]=(uint32_t)q; obit[q>>4]|=1<<((q>>1)&7); if(q<=r) SP[nSP++]=(uint32_t)q; }
    primesieve_free_iterator(&it); }
  LB_up=lg2_bound(B,1);
  for(size_t i=R0;i<R1;i++) RW[i].lp_dn=lg2_bound(RW[i].p-1,0);
  fprintf(stderr,"[rowverify] B=%llu rows %zu..%zu of %zu, %zu odd primes, %d threads (%.1fs)\n",(unsigned long long)B,R0,R1-1,nRW,nQ,NTH,now()-T0);
  /* stream */
  size_t np=R1-R0; tjob_t J[64]; pthread_t th[64];
  for(int t=0;t<NTH;t++){ J[t].q0=nQ*t/NTH; J[t].q1=nQ*(t+1)/NTH; J[t].S=calloc(np,sizeof(store_t)); J[t].pairs=0; pthread_create(&th[t],NULL,stream_worker,&J[t]); }
  long long pairs=0; for(int t=0;t<NTH;t++){ pthread_join(th[t],NULL); pairs+=J[t].pairs; }
  double ts=now()-T0;
  fprintf(stderr,"[rowverify] streaming done: %lld (p,q) pairs in %.1fs (%.3f us/pair/thread)\n",pairs,ts,1e6*ts*NTH/(double)(pairs?pairs:1));
  /* per row */
  int bad=0; size_t kept_tot=0;
  for(size_t r=0;r<np;r++){
    size_t nE=0,nS=0; for(int t=0;t<NTH;t++){ nE+=J[t].S[r].n; nS+=J[t].S[r].ns; }
    ent_t *E=malloc(sizeof(ent_t)*(nE+1)); uint64_t *SC=malloc(8*(nS+1)); size_t a=0,b=0;
    for(int t=0;t<NTH;t++){ memcpy(E+a,J[t].S[r].v,sizeof(ent_t)*J[t].S[r].n); a+=J[t].S[r].n; memcpy(SC+b,J[t].S[r].sc,8*J[t].S[r].ns); b+=J[t].S[r].ns; free(J[t].S[r].v); free(J[t].S[r].sc); }
    { qsort(SC,nS,8,cmp_u64); size_t w=0; for(size_t i=0;i<nS;i++) if(!w||SC[w-1]!=SC[i]) SC[w++]=SC[i]; nS=w; }
    kept_tot+=nE;
    bad += verify_row(&RW[R0+r],E,nE,SC,nS,stdout)!=0;
    free(E); free(SC);
  }
  printf("RESULT rows=%zu mismatching_rows=%d pairs=%lld kept_entries=%zu total=%.1fs\n",np,bad,pairs,kept_tot,now()-T0);
  return bad!=0; }
