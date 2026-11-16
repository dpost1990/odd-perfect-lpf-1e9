#!/usr/bin/env python3
"""
Independent replay checker for lpf.c proof logs (exact arithmetic, separate code).

usage: replay.py B rowsfile logfile [kn/kd] [odd|even]

1. Rows file (p -> admissible exponents a with the factorization of sigma(p^a)):
   every factorization is re-multiplied and compared with sigma(p^a) = (p^(a+1)-1)/(p-1) exactly,
   every factor must be an allowed prime (sympy.isprime, <= B, or a prime of k).
   (Completeness of the exponent lists is checked separately by rows_check.py.)
2. M_up: an independent rigorous upper bound for prod_{p in P} p/(p-1) (integer fixed point + Taylor bound for
   exp with explicit remainder, all in exact integers/Fractions).
3. Replays the depth-first search with exact Fractions and compares every event with the log of lpf.c,
   line by line.  Any difference -> FAIL.  Also checks the log ends with '# END nodes=... solutions=0'.
"""
import sys, math
from fractions import Fraction
import numpy as np
import sympy

sys.setrecursionlimit(100000)
B = int(sys.argv[1]); ROWS = sys.argv[2]; LOGF = sys.argv[3]
k = Fraction(sys.argv[4]) if len(sys.argv) > 4 else Fraction(2)
ODD = (sys.argv[5] if len(sys.argv) > 5 else 'odd') == 'odd'

def odd_primes_upto(n):
    # odd-only numpy sieve; index i <-> 2i+1
    s = np.ones(n // 2 + 1, dtype=bool); s[0] = False
    for i in range(1, (int(n ** 0.5) - 1) // 2 + 1):
        if s[i]:
            p = 2 * i + 1
            s[p * p // 2::p] = False
    return (2 * np.nonzero(s)[0] + 1).astype(np.int64)

print(f"[replay] B={B} k={k} odd={ODD}", flush=True)
OP = odd_primes_upto(B)
def iterP():
    if not ODD: yield 2
    for c in range(0, len(OP), 1 << 20):
        for x in OP[c:c + (1 << 20)].tolist(): yield x
Pset_odd = set()  # membership via binary search on OP instead of a huge set
def in_P(q):
    if q == 2: return (not ODD) and B >= 2
    if q > B or q % 2 == 0: return False
    i = np.searchsorted(OP, q)
    return i < len(OP) and OP[i] == q
kval = {}
for part, sgn in ((k.numerator, 1), (k.denominator, -1)):
    for q, e in sympy.factorint(part).items(): kval[q] = kval.get(q, 0) + sgn * e

# ---- 2. M_up ----
SC = 1 << 128
T = 0
for p in iterP():
    if p == 2:
        T += -(-SC * 6931471805599453095 // 10**19); continue   # log 2 <= 0.6931471805599453095
    if p < 2000:
        # exact series terms x^j/j (each rounded up) for j <= 60, tail <= x^61/(61(1-x)) <= 1.5*x^61/61
        for j in range(1, 61): T += -(-SC // (j * p ** j))
        T += -(-3 * SC // (2 * 61 * p ** 61))
    else:
        # -log(1-x) <= x + x^2/2 + x^3/3 + x^4/(4(1-x)) <= x + x^2/2 + x^3/3 + x^4/3
        T += -(-SC // p) + -(-SC // (2 * p * p)) + -(-SC // (3 * p ** 3)) + -(-SC // (3 * p ** 4))
y = Fraction(T, SC)
# exp(y) <= sum_{j<=J} y^j/j! + y^(J+1)/(J+1)! * (J+2)/(J+2-y)
J = 150; term = Fraction(1); S = Fraction(1)
for j in range(1, J + 1):
    term = term * y / j; S += term
term = term * y / (J + 1); S += term * Fraction(J + 2) / (J + 2 - y)
MUP = Fraction(-(-S.numerator * 2**96 // S.denominator), 2**96)   # round up
print(f"[replay] M_up = {float(MUP):.12f}", flush=True)

# ---- 1. rows ----
rows = {}
nf = 0
for line in open(ROWS):
    if not line.endswith('\n'): break
    parts = line.split()
    p = int(parts[0]); n = int(parts[1])
    adm = []
    for tok in parts[2:2 + n]:
        a_s, rest = tok.split(':', 1)
        a = int(a_s); items = rest.split(',')
        cnt = int(items[0]); f = []
        for it in items[1:]:
            q_s, e_s = it.split('^'); f.append((int(q_s), int(e_s)))
        assert len(f) == cnt
        sig = (p ** (a + 1) - 1) // (p - 1)
        prod = 1
        for q, e in f:
            assert sympy.isprime(q) and (in_P(q) or q in kval), (p, a, q)
            prod *= q ** e
        assert prod == sig, f"factorization mismatch p={p} a={a}"
        nf += 1
        adm.append((a, f))
    if p in rows: assert rows[p] == adm
    rows[p] = adm
print(f"[replay] rows: {len(rows)} primes, {nf} sigma factorizations verified exactly", flush=True)

# ---- 3. replay ----
logf = open(LOGF)
header = logf.readline()
assert header.startswith('#'), header
nodes = 0; nlines = 0
def expect(s):
    global nlines
    line = logf.readline().rstrip('\n')
    nlines += 1
    if line != s:
        print(f"[replay] MISMATCH at log line {nlines + 1}: expected {s!r}, log has {line!r}", flush=True)
        sys.exit(1)

assigned = {}; required = set(); excluded = set(); val = {}
sols = []
def kv(q): return kval.get(q, 0)

def dfs(depth, A, E):
    global nodes
    nodes += 1
    # lower bound
    LB = A
    for r in required: LB *= Fraction(r + 1, r)
    if LB > k: expect(f"{depth} LB"); return
    # upper bound (rigorous: true product <= MUP / E)
    if A < k and A * MUP / E < k: expect(f"{depth} UB"); return
    if required:
        r = max(required)
        required.discard(r)
        need = val.get(r, 0) - kv(r)
        for a, f in rows[r]:
            if a < need: continue
            if ODD and r != 2 and (a & 1) and val.get(2, 0) + 1 > kv(2): continue
            if any(q == r for q, e in f): expect(f"{depth} R {r} {a} self"); continue
            ok = True
            for q, e in f:
                nv = val.get(q, 0) + e
                if in_P(q):
                    if q in excluded:
                        if nv > kv(q): expect(f"{depth} R {r} {a} q{q} c1"); ok = False; break
                    elif q in assigned:
                        if nv > assigned[q] + kv(q): expect(f"{depth} R {r} {a} q{q} c2"); ok = False; break
                else:
                    if nv > kv(q): expect(f"{depth} R {r} {a} q{q} c3"); ok = False; break
            if not ok: continue
            if val.get(r, 0) > a + kv(r): expect(f"{depth} R {r} {a} selfval"); continue
            new_req = []
            for q, e in f:
                val[q] = val.get(q, 0) + e
                if in_P(q) and q not in kval and q not in assigned and q not in excluded and q not in required and q != r:
                    required.add(q); new_req.append(q)
            assigned[r] = a
            sig = (r ** (a + 1) - 1) // (r - 1)
            expect(f"{depth} A {r} {a}")
            dfs(depth + 1, A * Fraction(sig, r ** a), E * Fraction(r, r - 1))
            del assigned[r]
            for q in new_req: required.discard(q)
            for q, e in f: val[q] -= e
        required.add(r)
        return
    forced = [q for q in kval if in_P(q) and q not in assigned and q not in excluded and val.get(q, 0) > kval[q]]
    if forced:
        for q in forced: required.add(q)
        expect(f"{depth} F"); dfs(depth + 1, A, E)
        for q in forced: required.discard(q)
        return
    if A == k:
        good = all(val.get(q, 0) == a + kv(q) for q, a in assigned.items())
        good = good and all(val.get(q, 0) == e for q, e in kval.items() if q not in assigned)
        good = good and all(v == 0 or q in assigned or q in kval for q, v in val.items())
        if good and assigned:
            N = 1
            for q, a in assigned.items(): N *= q ** a
            assert sympy.divisor_sigma(N) * k.denominator == k.numerator * N
            sols.append(N); expect(f"{depth} SOL {N}")
        else:
            expect(f"{depth} EQ")
        return
    if A > k: expect(f"{depth} OVER"); return
    p = None
    for q in iterP():
        if q not in assigned and q not in excluded:
            p = q; break
    if p is None: expect(f"{depth} NOFREE"); return
    required.add(p); expect(f"{depth} I {p}"); dfs(depth + 1, A, E); required.discard(p)
    excluded.add(p); expect(f"{depth} X {p}"); dfs(depth + 1, A, E * Fraction(p, p - 1)); excluded.discard(p)

for q, e in kval.items():
    if e < 0: required.add(q)
dfs(0, Fraction(1), Fraction(1))
tail = logf.readline().strip()
assert tail == f"# END nodes={nodes} solutions={len(sols)}", (tail, nodes, len(sols))
print(f"[replay] OK: {nodes} nodes, {nlines} log lines matched, solutions={sols}", flush=True)
