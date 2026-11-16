#!/usr/bin/env python3
"""
Independent, memory-light re-computation of lpf.c rows for large B (up to 2^31), used on a SAMPLE of rows.
Separate code (numpy + Python integers).  For a prime p:
  * streams over all odd primes q <= B in chunks, computes o = ord_q(p) (numpy, products < 2^62),
    and w = [p^o == 1 mod q^2] with exact Python integers;
  * records (o, q) when o <= OM (OM = 2*10^6) or w;  for o > OM and not w it checks
        floor((B-1)/o) * log B + log o + 1 < phi(o) * log(p-1)
    (phi(o) from the factorisation of q-1) -- if that fails, o is recorded for exact treatment;
  * for every recorded order d: exact bucket = all primes q = 1 (mod d) (step 2d for odd d) with ord_q(p) = d,
    found by scanning that progression; candidate test with true bucket sums; Phi_d(p) exactly with Python
    integers, divided by bucket primes and P(d); good iff quotient 1;  admissible a <=> all e | a+1 good.
  * compares with the row written by lpf.c.
usage: rows_check_big.py B rowsfile p1,p2,...
"""
import sys, math, time
import numpy as np
import sympy

B = int(sys.argv[1]); ROWS = sys.argv[2]; PLIST = [int(x) for x in sys.argv[3].split(',')]
OM = 2_000_000
t0 = time.time()
# odd prime bitmap / list
sieve = np.ones(B // 2 + 1, dtype=bool); sieve[0] = False
for i in range(1, (math.isqrt(B) - 1) // 2 + 1):
    if sieve[i]:
        p = 2 * i + 1; sieve[p * p // 2::p] = False
Q = (2 * np.nonzero(sieve)[0] + 1).astype(np.int64)
def isprime_odd_vec(x): return sieve[x // 2] & (x % 2 == 1)
small = Q[Q <= math.isqrt(B) + 1].tolist()
print(f"[big] B={B}: {len(Q)} odd primes ({time.time()-t0:.0f}s)", flush=True)

def powmod_vec(base, e, m):
    base = base % m; r = np.ones_like(m); e = e.copy()
    while (e > 0).any():
        odd = (e & 1) == 1
        r = np.where(odd, (r * base) % m, r)
        e >>= 1; base = (base * base) % m
    return r

def factor_chunk(q):
    """distinct prime factors of q-1 (q: sorted chunk of odd primes) as list of (prime, index-array) plus the
    cofactor (1 or a prime > sqrt(B)).  Odd l: the q = 1 (mod 2l) are found by walking the progression."""
    rem = q - 1; facs = [(2, np.arange(len(q)))]
    while True:
        mm = rem % 2 == 0
        if not mm.any(): break
        rem[mm] //= 2
    qlo = int(q[0]); qhi = int(q[-1])
    for l in small:
        st = qlo + ((1 - qlo) % (2 * l))
        if st > qhi: continue
        cand = np.arange(st, qhi + 1, 2 * l, dtype=np.int64)
        pos = np.searchsorted(q, cand); pos = pos[pos < len(q)]
        m = pos[q[pos] == cand[:len(pos)]] if len(pos) else pos
        if len(m) == 0: continue
        facs.append((l, m))
        sub = rem[m]
        while True:
            mm = sub % l == 0
            if not mm.any(): break
            sub[mm] //= l
        rem[m] = sub
    return facs, rem

def order_chunk(p, q):
    facs, cof = factor_chunk(q)
    o = q - 1; pv = np.full_like(q, p)
    for l, idx in facs:
        qq = q[idx]; oo = o[idx]; fe = np.ones_like(oo); t = oo.copy()
        while True:
            mm = t % l == 0
            if not mm.any(): break
            fe[mm] *= l; t[mm] //= l
        oo = oo // fe
        y = powmod_vec(pv[idx], oo, qq)
        while True:
            ne = y != 1
            if not ne.any(): break
            y[ne] = powmod_vec(y[ne], np.full(int(ne.sum()), l, dtype=np.int64), qq[ne]); oo[ne] *= l
        o[idx] = oo
    bi = np.nonzero(cof > 1)[0]
    if len(bi):
        qq = q[bi]; oo = o[bi]; L = cof[bi]
        fe = np.where(oo % L == 0, L, 1); oo = oo // fe
        y = powmod_vec(pv[bi], oo, qq); ne = y != 1; oo[ne] *= L[ne]; o[bi] = oo
    assert (powmod_vec(pv, o, q) == 1).all()
    # phi(o)/o from the prime factors of q-1
    ratio = np.ones(len(q))
    for l, idx in facs:
        h = idx[o[idx] % l == 0]; ratio[h] *= (1 - 1 / l)
    h = bi[o[bi] % cof[bi] == 0]; ratio[h] *= (1 - 1 / cof[h].astype(np.float64))
    return o, ratio

def vq(p, d, q):
    v = 0; m = q
    while pow(p, d, m) == 1: v += 1; m *= q
    return v

def check(p, claimed):
    lnB = math.log(B); lnp1 = math.log(p - 1)
    rec = {}   # d -> True (recorded, needs exact bucket)
    t = time.time()
    CH = 1 << 22
    for c in range(0, len(Q), CH):
        q = Q[c:c + CH]; q = q[q != p]
        o, ratio = order_chunk(p, q)
        ol = o.tolist(); ql = q.tolist()
        # Wieferich-type flags with exact integers
        for oi, qi in zip(ol, ql):
            if oi <= OM: rec.setdefault(oi, []).append(qi)
            elif pow(p, oi, qi * qi) == 1: rec[oi] = None
        big = o > OM
        lhs = ((B - 1) // np.maximum(o, 1)).astype(np.float64) * lnB + np.log(o.astype(np.float64)) + 1.0
        rhs = o.astype(np.float64) * ratio * lnp1
        fail = big & ~(lhs < rhs)
        for oi in o[fail].tolist(): rec[oi] = None
    if ((p + 1) & p) == 0: rec.setdefault(2, [])
    good = {}
    for d in sorted(rec):
        if d < 2: continue
        fs = sympy.primefactors(d)
        if rec[d] is not None:
            bucket = sorted(rec[d])          # complete: every q with ord_q(p) = d <= OM was seen in the stream
        else:                                 # large recorded order: scan the progression q = 1 mod d
            step = 2 * d if d % 2 else d
            cand = np.arange(1 + step, B + 1, step, dtype=np.int64)
            cand = cand[isprime_odd_vec(cand)]; cand = cand[cand != p]
            if len(cand):
                pd = powmod_vec(np.full_like(cand, p), np.full_like(cand, d), cand)
                cand = cand[pd == 1]
            bucket = [qi for qi in cand.tolist() if all(pow(p, d // f, qi) != 1 for f in fs)]
        Pd = max(fs); Pd_ok = Pd <= B
        if d > 2:
            s = sum(vq(p, d, qi) * math.log(qi) for qi in bucket) + (math.log(Pd) if Pd_ok else 0.0)
            if s < sympy.totient(d) * lnp1 - 1.0: continue
        num = den = 1
        for e in sympy.divisors(d):
            mu = sympy.mobius(d // e)
            if mu == 1: num *= p ** e - 1
            elif mu == -1: den *= p ** e - 1
        ph = num // den; f = {}
        for qq in bucket + ([Pd] if Pd_ok else []):
            while ph % qq == 0: ph //= qq; f[qq] = f.get(qq, 0) + 1
        if ph == 1: good[d] = f
    adm = []
    for d in sorted(good):
        if all(e in good for e in sympy.divisors(d) if e > 1):
            F = {}
            for e in sympy.divisors(d):
                if e > 1:
                    for qq, ee in good[e].items(): F[qq] = F.get(qq, 0) + ee
            adm.append((d - 1, tuple(sorted(F.items()))))
    theirs = sorted((a, tuple(sorted(f))) for a, f in claimed)
    return sorted(adm) == theirs, sorted(adm), theirs, len(rec), time.time() - t

rows = {}
for line in open(ROWS):
    if not line.endswith('\n'): break
    parts = line.split(); p = int(parts[0]); n = int(parts[1]); adm = []
    for tok in parts[2:2 + n]:
        a_s, rest = tok.split(':', 1); items = rest.split(',')
        adm.append((int(a_s), [(int(x.split('^')[0]), int(x.split('^')[1])) for x in items[1:]]))
    rows[p] = adm
bad = 0
for p in PLIST:
    if p not in rows: print(f"[big] p={p} not (yet) in rows file", flush=True); continue
    ok, mine, theirs, nrec, dt = check(p, rows[p])
    bad += (not ok)
    print(f"[big] p={p} ok={ok} recorded_orders={nrec} adm={len(mine)} {dt:.0f}s", flush=True)
    if not ok: print(f"   checker {mine}\n   lpf     {theirs}", flush=True)
print(f"[big] DONE mismatches={bad}", flush=True)
