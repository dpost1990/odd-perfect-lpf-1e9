#!/usr/bin/env python3
"""
Smooth sigma-closure solver (ideas agent, prototype A).

Finds ALL N whose prime factors are all <= B (optionally odd only) with sigma(N) = k*N.
Used as a benchmark/proxy for the OPN factor-chain tree:
  * k=2, odd  -> "no B-smooth odd perfect number"  (known: largest prime of an OPN > 1e8,
                  Goto-Ohno 2008, so every run here is VALIDATION, not new)
  * k=2/3/4, even allowed -> positive control: must find the known perfect / multiperfect numbers.

Ideas that can be switched on/off (to measure their effect):
  ORD   : Zsigmondy/ord exponent lemma.  If p^a || N then for every d | a+1, d>1, sigma(p^a) contains
          Phi_d(p), which (Bang-Zsigmondy) has a primitive prime divisor q with ord_q(p) = d.
          q | sigma(N) = kN, so q | kN.  Hence the admissible a+1 are exactly the d whose divisors >1
          all lie in O(p) = {ord_q(p) : q allowed prime}.  This makes the exponent set FINITE and
          complete (no exponent cap), and lets exclusions of primes shrink exponent sets.
          (Exceptions to Zsigmondy: p=2,d=6 ; d=2 with p+1 a power of 2 -> always allowed.)
          Without ORD we use a naive cap A <= ACAP (incomplete!).
  VLB   : valuation lower bound: when assigning exponent a to required prime r, a + v_r(k) >= current
          accumulated v_r(prod sigma) (since valuations only grow).
  ORDER : which required prime to branch on first: 'small' or 'large'.
  UB    : abundancy upper bound with all still-possible primes at infinite exponent.
"""
import sys, math, time
from functools import lru_cache
import argparse

def primes_upto(n):
    s = bytearray([1]) * (n + 1); s[0:2] = b'\x00\x00'
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n + 1) if s[i]]

def mult_order(a, q):
    # order of a mod prime q (a not divisible by q)
    n = q - 1
    o = n
    m = n; f = 2; fs = []
    while f * f <= m:
        if m % f == 0:
            fs.append(f)
            while m % f == 0: m //= f
        f += 1
    if m > 1: fs.append(m)
    for f in fs:
        while o % f == 0 and pow(a, o // f, q) == 1:
            o //= f
    return o

@lru_cache(maxsize=None)
def prime_factors(n):
    fs = []; f = 2
    while f * f <= n:
        if n % f == 0:
            fs.append(f)
            while n % f == 0: n //= f
        f += 1
    if n > 1: fs.append(n)
    return tuple(fs)

def mobius(n):
    r = 1; f = 2
    while f * f <= n:
        if n % f == 0:
            n //= f
            if n % f == 0: return 0
            r = -r
        f += 1
    if n > 1: r = -r
    return r

def divisors(n):
    ds = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            ds.append(i)
            if i != n // i: ds.append(n // i)
        i += 1
    return sorted(ds)

class Solver:
    def __init__(self, B, k, odd, use_ord=True, use_cyclo=True, use_vlb=True, order='large', use_ub=True,
                 acap=60, node_limit=None, time_limit=None, verbose=False):
        self.B, self.k, self.odd = B, k, odd
        self.P = [p for p in primes_upto(B) if not (odd and p == 2)]
        self.Pset = set(self.P)
        self.use_ord, self.use_vlb, self.order, self.use_ub = use_ord, use_vlb, order, use_ub
        self.acap = acap
        self.nodes = 0
        self.sigma_evals = 0
        self.solutions = []
        self.node_limit, self.time_limit = node_limit, time_limit
        self.t0 = time.time()
        self.aborted = False
        self.verbose = verbose
        # primes dividing k (target valuations for primes outside the support)
        # k may be an int or a Fraction; kval[q] = v_q(k) (negative for denominator primes)
        from fractions import Fraction
        self.k = k = Fraction(k)
        self.kval = {}
        for part, sgn in ((k.numerator, 1), (k.denominator, -1)):
            kk = part
            for q in primes_upto(max(2, kk)) if kk < 10**6 else []:
                while kk % q == 0:
                    self.kval[q] = self.kval.get(q, 0) + sgn; kk //= q
            assert kk == 1, "k numerator/denominator must be < 1e6"
        self.den_required = frozenset(q for q, e in self.kval.items() if e < 0)
        # all primes that may appear in sigma(N) = kN
        self.allowed_sigma_primes = set(self.P) | set(self.kval)
        self.logw = {p: math.log(p / (p - 1)) for p in self.P}
        # ord table: O[p][q] = ord_q(p)
        self._ordt = {}
        self._qfac = {}
        self._sfc = {}; self._pfc = {}; self._byord = {}; self._expc = {}
        self.use_cyclo = use_cyclo

    def ord_row(self, p):
        r = self._ordt.get(p)
        if r is None:
            r = {}
            for q in self.allowed_sigma_primes:
                if q == p or p % q == 0: continue
                fs = self._qfac.get(q)
                if fs is None:
                    m = q - 1; fs = []; f = 2
                    while f * f <= m:
                        if m % f == 0:
                            fs.append(f)
                            while m % f == 0: m //= f
                        f += 1
                    if m > 1: fs.append(m)
                    self._qfac[q] = fs
                o = q - 1
                for f in fs:
                    while o % f == 0 and pow(p, o // f, q) == 1: o //= f
                r[q] = o
            self._ordt[p] = r
        return r

    # --- exponent candidates for prime p given currently excluded primes
    def exp_candidates(self, p, excluded):
        if not self.use_ord:
            return list(range(1, self.acap + 1))
        if self.use_cyclo:
            # fast path: d is admissible iff Phi_e(p) is smooth over allowed primes for every e | d, e > 1
            # (exclusions are enforced later in dfs when sigma's factors are inspected)
            c = self._expc.get(p)
            if c is None:
                D = set(self.ord_row(p).values())
                if p == 2: D.add(6)
                if ((p + 1) & p) == 0: D.add(2)
                good = set(d for d in D if d >= 2 and self.phi_fact(p, d) is not None)
                c = sorted(d - 1 for d in good if all(e in good for e in divisors(d) if e > 1))
                self._expc[p] = c
            return c
        O = set(o for q, o in self.ord_row(p).items() if q not in excluded or q in self.kval)
        mersenne_like = ((p + 1) & p) == 0  # p+1 power of two
        # d allowed iff every divisor e>1 of d is in O (or Zsigmondy exception)
        def ok_e(e):
            if e in O: return True
            if p == 2 and e == 6: return True
            if e == 2 and mersenne_like: return True
            return False
        # d itself must be "ok", so candidates are d in O (plus exceptions) whose divisors are all ok
        D = set(O)
        if p == 2: D.add(6)
        if mersenne_like: D.add(2)
        cands = []
        for d in sorted(D):
            if d < 2: continue
            if all(ok_e(e) for e in divisors(d) if e > 1):
                cands.append(d - 1)
        return cands

    def sigma_fact(self, p, a):
        """factor sigma(p^a) over allowed primes; return dict or None if not smooth."""
        key = (p, a)
        if key in self._sfc: return self._sfc[key]
        if self.use_cyclo:
            f = {}
            # check small d first so non-smooth candidates are rejected cheaply
            for d in divisors(a + 1):
                if d < 2: continue
                g = self.phi_fact(p, d)
                if g is None: f = None; break
                for q, e in g.items(): f[q] = f.get(q, 0) + e
            self._sfc[key] = f
            return f
        self.sigma_evals += 1
        s = (p ** (a + 1) - 1) // (p - 1)
        f = {}
        for q in self.allowed_sigma_primes_sorted:
            if q * q > s: break
            if s % q == 0:
                e = 0
                while s % q == 0: s //= q; e += 1
                f[q] = e
        if s > 1:
            if s in self.allowed_sigma_primes: f[s] = f.get(s, 0) + 1
            else: f = None
        self._sfc[key] = f
        return f

    def phi_fact(self, p, d):
        """CYCLO idea: factor Phi_d(p) using only primes q with ord_q(p) = d, or q | d
        (every prime factor of Phi_d(p) is of that form).  Cached per (p, d)."""
        key = (p, d)
        if key in self._pfc: return self._pfc[key]
        byord = self._byord.get(p)
        if byord is None:
            byord = {}
            for q, o in self.ord_row(p).items(): byord.setdefault(o, []).append(q)
            self._byord[p] = byord
        # cheap size filter: the q with ord_q(p)=d (q not | d) contribute v_q(p^d-1); together with the
        # prime factors of d they must account for all of Phi_d(p) ~ p^phi(d).
        if d > 2:
            pfd = prime_factors(d)
            phid = d
            for r in pfd: phid = phid // r * (r - 1)
            tot = sum(math.log(r) * 2 for r in pfd)  # generous allowance for q | d
            for q in byord.get(d, []):
                if q in pfd: continue
                e = 1; qq = q * q
                while pow(p, d, qq) == 1: e += 1; qq *= q
                tot += e * math.log(q)
            if tot < phid * math.log(p - 1) - 1e-6:  # Phi_d(p) > (p-1)^phi(d)
                self._pfc[key] = None
                return None
        self.sigma_evals += 1
        # Phi_d(p) via Moebius product over divisors
        num = den = 1
        for e in divisors(d):
            m = mobius(d // e)
            if m == 1: num *= p ** e - 1
            elif m == -1: den *= p ** e - 1
        v = num // den
        f = {}
        cand = list(byord.get(d, []))
        for q in prime_factors(d):
            if q in self.allowed_sigma_primes and q not in cand: cand.append(q)
        for q in cand:
            if v % q == 0:
                e = 0
                while v % q == 0: v //= q; e += 1
                f[q] = e
        res = f if v == 1 else None
        self._pfc[key] = res
        return res

    def run(self):
        self.allowed_sigma_primes_sorted = sorted(self.allowed_sigma_primes)
        logS = sum(self.logw.values())
        try:
            if not self.den_required <= self.Pset: return self
            self.dfs({}, self.den_required, frozenset(), {}, 1, 1, logS)
        except TimeoutError:
            self.aborted = True
        return self

    def check_limits(self):
        self.nodes += 1
        if self.node_limit and self.nodes > self.node_limit: raise TimeoutError
        if self.time_limit and (self.nodes & 1023) == 0 and time.time() - self.t0 > self.time_limit:
            raise TimeoutError

    def L(self, depth, msg):
        if getattr(self,'logf',None): self.logf.write(f'{depth} {msg}\n')

    def dfs(self, assigned, required, excluded, val, num, den, logS, depth=0):
        # assigned: {p:a}; required: primes that must divide N, not assigned
        # val: accumulated valuations of prod sigma(p^a) over assigned
        # num/den: abundancy of assigned part ; logS: sum log(p/(p-1)) over free+required primes
        self.check_limits()
        k = self.k
        # lower bound: A * prod_{required}(1+1/r) <= k
        if required:
            lnum, lden = num, den
            for r in required: lnum *= (r + 1); lden *= r
            if lnum > k * lden: self.L(depth,'LB'); return
        elif num > k * den:
            self.L(depth,'LB'); return
        # upper bound
        if self.use_ub:
            if num < k * den and math.log(num / den) + logS < math.log(k) - 1e-6:  # generous margin for float error (prototype; use interval arithmetic for a proof)
                self.L(depth,'UB'); return
        if required:
            # choose a required prime
            r = max(required) if self.order == 'large' else min(required)
            req2 = required - {r}
            need = val.get(r, 0) - self.kval.get(r, 0)
            for a in self.exp_candidates(r, excluded):
                if self.use_vlb and a < need: continue
                if self.odd and k == 2 and (a & 1) and val.get(2, 0) >= 1: continue  # parity prefilter
                f = self.sigma_fact(r, a)
                if f is None: continue
                if r in f: continue
                ok = True
                nval = dict(val)
                nreq = set(req2)
                for q, e in f.items():
                    nval[q] = nval.get(q, 0) + e
                    if q in excluded:
                        if nval[q] > self.kval.get(q, 0): ok = False; break
                        continue
                    if q in assigned:
                        if nval[q] > assigned[q] + self.kval.get(q, 0): ok = False; break
                    elif q == r:
                        ok = False; break
                    elif q in self.Pset and q not in self.kval:
                        nreq.add(q)
                    elif q in self.Pset:
                        pass  # q | k: may be supplied by k; decided when required set empties
                    else:  # q divides k but cannot be in support (e.g. 2 for odd N)
                        if nval[q] > self.kval.get(q, 0): ok = False; break
                if not ok: continue
                # r itself: accumulated val[r] must not exceed a + v_r(k)
                if nval.get(r, 0) > a + self.kval.get(r, 0): continue
                na = dict(assigned); na[r] = a
                s = (r ** (a + 1) - 1) // (r - 1)
                nnum, nden = num * s, den * r ** a
                g = math.gcd(nnum, nden); nnum //= g; nden //= g
                # logS: r leaves the free/required pool; newly required primes were already in pool
                self.L(depth,f'A {r} {a}')
                self.dfs(na, frozenset(nreq), excluded, nval, nnum, nden, logS - self.logw[r], depth+1)
            return
        # required empty: primes dividing k that overflow their k-valuation must be in the support
        forced = [q for q in self.kval if q in self.Pset and q not in assigned and q not in excluded
                  and val.get(q, 0) > self.kval[q]]
        if forced:
            self.L(depth,'F')
            self.dfs(assigned, frozenset(forced), excluded, val, num, den, logS, depth+1)
            return
        if num * 1 == k * den:
            # check all valuations exact
            good = all(val.get(q, 0) == a + self.kval.get(q, 0) for q, a in assigned.items())
            good = good and all(val.get(q, 0) == e for q, e in self.kval.items() if q not in assigned)
            if good and assigned:
                N = 1
                for q, a in assigned.items(): N *= q ** a
                self.solutions.append(N)
                if self.verbose: print('SOLUTION', N, sorted(assigned.items()), flush=True)
            return
        if num > k * den: return
        # need more primes: branch include/exclude on smallest free prime
        free = [p for p in self.P if p not in assigned and p not in excluded]
        if not free: return
        p = free[0]
        # include
        self.L(depth,f'I {p}')
        self.dfs(assigned, frozenset([p]), excluded, val, num, den, logS, depth+1)
        # exclude
        self.L(depth,f'X {p}')
        self.dfs(assigned, required, excluded | {p}, val, num, den, logS - self.logw[p], depth+1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--B', type=int, default=100)
    ap.add_argument('--k', type=str, default='2')
    ap.add_argument('--odd', action='store_true')
    ap.add_argument('--no-ord', action='store_true')
    ap.add_argument('--no-vlb', action='store_true')
    ap.add_argument('--no-cyclo', action='store_true')
    ap.add_argument('--no-ub', action='store_true')
    ap.add_argument('--order', default='large')
    ap.add_argument('--acap', type=int, default=60)
    ap.add_argument('--node-limit', type=int, default=None)
    ap.add_argument('--time-limit', type=float, default=None)
    ap.add_argument('-v', action='store_true')
    a = ap.parse_args()
    t = time.time()
    from fractions import Fraction
    s = Solver(a.B, Fraction(a.k), a.odd, use_ord=not a.no_ord, use_cyclo=not a.no_cyclo, use_vlb=not a.no_vlb, order=a.order,
               use_ub=not a.no_ub, acap=a.acap, node_limit=a.node_limit, time_limit=a.time_limit,
               verbose=a.v).run()
    print(f"B={a.B} k={a.k} odd={a.odd} ord={not a.no_ord} cyclo={not a.no_cyclo} vlb={not a.no_vlb} ub={not a.no_ub} "
          f"order={a.order} nodes={s.nodes} sigma_evals={s.sigma_evals} aborted={s.aborted} "
          f"time={time.time()-t:.2f}s solutions={sorted(s.solutions)}")

if __name__ == '__main__':
    main()
