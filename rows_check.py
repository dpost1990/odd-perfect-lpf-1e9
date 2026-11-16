#!/usr/bin/env python3
"""
Independent re-computation of the "rows" of lpf.c (admissible exponents of p and sigma(p^a) factorizations).
Separate code, separate method (numpy vectorised; exact Python integers for all final decisions):

  for every odd prime q <= B, q != p:  o = ord_q(p)     (q-1 factored by vectorised trial division)
                                       w = [p^o == 1 mod q^2]  (Wieferich-type flag; v_q(Phi_o(p)) >= 2)
  For EVERY order o that occurs: S(o) = sum_{q: ord_q(p)=o} v_q log q  (v_q = 1 unless w, else exact)
  d is a candidate iff  S(d) + log P(d) >= phi(d) log(p-1) - 1  (otherwise Phi_d(p) > (p-1)^phi(d) cannot be
  smooth), plus the Zsigmondy exceptions (d=2 if p+1 is a power of 2).  Unlike lpf.c no "(B/o) log B" bound
  is used: the true bucket sums of all orders are computed.
  Each candidate: Phi_d(p) computed exactly and divided by its bucket primes and P(d) -> good iff quotient 1.
  admissible a  <=>  every e | a+1, e > 1, is good.   Compare with the rows file of lpf.c.

usage: rows_check.py B rowsfile [mode] [args]
   mode 'all'            : check every row in the file
   mode 'sample N SEED'  : check N random rows (+ every row with p < 1000)
   mode 'list p1,p2,...' : check given primes
"""
import sys, math, random, time
import numpy as np
import sympy

B = int(sys.argv[1]); ROWS = sys.argv[2]
mode = sys.argv[3] if len(sys.argv) > 3 else 'all'
ALLOW2 = True   # odd-perfect mode: 2 may occur in sigma (v_2 = 1)

def odd_primes_upto(n):
    s = np.ones(n // 2 + 1, dtype=bool); s[0] = False
    for i in range(1, (int(n ** 0.5) - 1) // 2 + 1):
        if s[i]:
            p = 2 * i + 1
            s[p * p // 2::p] = False
    return (2 * np.nonzero(s)[0] + 1).astype(np.int64)

t0 = time.time()
Q = odd_primes_upto(B)
# factor q-1: slots of distinct primes (vectorised trial division by primes <= sqrt(B)), cofactor is 1 or prime
n = Q - 1
rem = n.copy()
slots = []   # list of (prime, mask)
for l in [2] + odd_primes_upto(int(math.isqrt(B)) + 1).tolist():
    m = (rem % l == 0)
    if not m.any(): continue
    slots.append((l, np.nonzero(m)[0]))
    sub = rem[m]
    while True:
        mm = (sub % l == 0)
        if not mm.any(): break
        sub[mm] //= l
    rem[m] = sub
big = rem  # 1 or a prime > sqrt(B)
print(f"[rows_check] B={B}: {len(Q)} odd primes, q-1 factored in {time.time()-t0:.1f}s", flush=True)

def powmod_vec(base, e, m):
    """base^e mod m elementwise, m < 2^31.5 so products fit in int64"""
    base = base % m; r = np.ones_like(m); e = e.copy()
    while True:
        nz = e > 0
        if not nz.any(): break
        odd = (e & 1) == 1
        r = np.where(odd, (r * base) % m, r)
        e >>= 1
        base = (base * base) % m
    return r

def mulmod_big(a, b, m):
    """a*b mod m for m < 2^54 (q^2 with q < 1.3e8) using a float quotient estimate + exact wrap-around"""
    qh = np.floor(a.astype(np.float64) * b.astype(np.float64) / m.astype(np.float64)).astype(np.int64)
    r = (a.astype(np.uint64) * b.astype(np.uint64) - qh.astype(np.uint64) * m.astype(np.uint64)).view(np.int64)
    for _ in range(40):
        lo = r < 0; hi = r >= m
        if not (lo.any() or hi.any()): break
        r = np.where(lo, r + m, np.where(hi, r - m, r))
    assert not ((r < 0) | (r >= m)).any()
    return r

def powmod_big(base, e, m):
    base = base % m; r = np.ones_like(m); e = e.copy()
    while (e > 0).any():
        odd = (e & 1) == 1
        if odd.any(): r = np.where(odd, mulmod_big(r, base, m), r)
        e >>= 1
        base = mulmod_big(base, base, m)
    return r

def check_prime(p, claimed):
    keep = Q != p
    q = Q[keep]; idx_map = np.nonzero(keep)[0]
    pos = np.full(len(Q), -1, dtype=np.int64); pos[idx_map] = np.arange(len(q))
    o = q - 1
    pv = np.full_like(q, p)
    # ord via the standard algorithm, one prime of q-1 at a time
    def handle(l, idx):
        idx = pos[idx]; idx = idx[idx >= 0]
        if len(idx) == 0: return
        qq = q[idx]; oo = o[idx]
        fe = np.ones_like(oo)
        t = oo.copy()
        while True:
            mm = (t % l == 0)
            if not mm.any(): break
            fe[mm] *= l; t[mm] //= l
        oo = oo // fe
        y = powmod_vec(pv[idx], oo, qq)
        while True:
            ne = y != 1
            if not ne.any(): break
            y[ne] = powmod_vec(y[ne], np.full(ne.sum(), l, dtype=np.int64), qq[ne])
            oo[ne] *= l
        o[idx] = oo
    for l, idx in slots: handle(l, idx)
    bigidx = np.nonzero(big[idx_map] > 1)[0]
    if len(bigidx):
        # cofactor primes (distinct per q): treat them as one more slot, element-wise prime
        qq = q[bigidx]; oo = o[bigidx]; L = big[idx_map][bigidx]
        fe = np.where(oo % L == 0, L, 1)
        oo = oo // fe
        y = powmod_vec(pv[bigidx], oo, qq)
        ne = y != 1
        oo[ne] *= L[ne]
        o[bigidx] = oo
    assert (powmod_vec(pv, o, q) == 1).all()
    # Wieferich-type flags
    w = powmod_big(pv, o, q * q) == 1
    # exact v for flagged q
    lnq = np.log(q.astype(np.float64)); contrib = lnq.copy()
    for i in np.nonzero(w)[0]:
        qi = int(q[i]); oi = int(o[i]); v = 1
        while pow(p, oi, qi ** (v + 1)) == 1: v += 1
        contrib[i] = v * math.log(qi)
    # group by order
    order = np.argsort(o, kind='stable'); os_ = o[order]
    uniq, starts = np.unique(os_, return_index=True)
    S = np.add.reduceat(contrib[order], starts)
    # phi(o) and largest prime factor of o, from the factorisation of q-1 (first element of each group)
    first = order[starts]
    phi = uniq.astype(np.float64); Pd = np.ones_like(uniq)
    rep = idx_map[first]   # indices into Q of representatives
    inv = np.full(len(Q), -1, dtype=np.int64); inv[rep] = np.arange(len(uniq))
    for l, idx in slots:
        g = inv[idx]; g = g[g >= 0]
        if len(g) == 0: continue
        hit = (uniq[g] % l == 0)
        gg = g[hit]; phi[gg] *= (1.0 - 1.0 / l); Pd[gg] = np.maximum(Pd[gg], l)
    bg = big[rep]; hit = (bg > 1) & (uniq % np.maximum(bg, 1) == 0)
    phi[hit] *= (1.0 - 1.0 / bg[hit]); Pd[hit] = np.maximum(Pd[hit], bg[hit])
    lnp1 = math.log(p - 1)
    allowP = np.log(np.maximum(Pd, 1).astype(np.float64))
    cand = uniq[(uniq >= 2) & ((uniq <= 2) | (S + allowP >= phi * lnp1 - 1.0))].tolist()
    if ((p + 1) & p) == 0 and 2 not in cand: cand.append(2)
    good = {}
    for d in sorted(cand):
        lo_ = np.searchsorted(os_, d, 'left'); hi_ = np.searchsorted(os_, d, 'right'); bucket = q[order[lo_:hi_]].tolist()
        num = den = 1
        for e in sympy.divisors(d):
            mu = sympy.mobius(d // e)
            if mu == 1: num *= p ** e - 1
            elif mu == -1: den *= p ** e - 1
        ph = num // den
        f = {}
        PdP = max(sympy.primefactors(d))
        for qq in bucket + ([PdP] if (PdP <= B or (PdP == 2 and ALLOW2)) else []):
            while ph % qq == 0: ph //= qq; f[qq] = f.get(qq, 0) + 1
        if ph == 1: good[d] = f
    adm = []
    for d in sorted(good):
        if all(e in good for e in sympy.divisors(d) if e > 1):
            F = {}
            for e in sympy.divisors(d):
                if e > 1:
                    for qq, ee in good[e].items(): F[qq] = F.get(qq, 0) + ee
            adm.append((d - 1, F))
    mine = sorted((a, tuple(sorted(F.items()))) for a, F in adm)
    theirs = sorted((a, tuple(sorted(dict(f).items()))) for a, f in claimed)
    return mine == theirs, mine, theirs, len(uniq), len(cand)

rows = {}
for line in open(ROWS):
    if not line.endswith('\n'): break
    parts = line.split(); p = int(parts[0]); nadm = int(parts[1]); adm = []
    for tok in parts[2:2 + nadm]:
        a_s, rest = tok.split(':', 1); items = rest.split(',')
        adm.append((int(a_s), [(int(x.split('^')[0]), int(x.split('^')[1])) for x in items[1:]]))
    rows[p] = adm
ps = sorted(rows)
if mode == 'sample':
    N = int(sys.argv[4]); seed = int(sys.argv[5]); random.seed(seed)
    ps = sorted(set([x for x in ps if x < 1000] + random.sample(ps, min(N, len(ps)))))
elif mode == 'random':
    N = int(sys.argv[4]); seed = int(sys.argv[5]); random.seed(seed)
    big_ = [x for x in ps if x >= 1000]; ps = sorted(random.sample(big_, min(N, len(big_))))
elif mode == 'small':
    ps = [x for x in ps if x < 1000]
elif mode == 'list':
    ps = [int(x) for x in sys.argv[4].split(',')]
bad = 0
for i, p in enumerate(ps):
    t = time.time()
    ok, mine, theirs, nord, ncand = check_prime(p, rows[p])
    if not ok:
        bad += 1; print(f"[rows_check] MISMATCH p={p}\n  checker: {mine}\n  lpf:     {theirs}", flush=True)
    if i % 10 == 0 or not ok:
        print(f"[rows_check] {i+1}/{len(ps)} p={p} ok={ok} orders={nord} candidates={ncand} adm={len(mine)} {time.time()-t:.1f}s", flush=True)
print(f"[rows_check] DONE {len(ps)} rows checked, mismatches={bad}", flush=True)
