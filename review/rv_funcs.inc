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
