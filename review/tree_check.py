#!/usr/bin/env python3
"""
tree_check.py -- independent PROOF-TREE checker for lpf.c logs (review copy, written from scratch).

Different derivation from replay.py.  replay.py re-runs the same depth-first search (same branching order,
same incremental bookkeeping) and demands the identical event stream.  This checker does NOT search.  It reads
the log as a tree and checks that every node is a valid step of a proof, recomputing everything from scratch
from the path (assigned exponents, excluded primes, included primes):

  semantics of a node:  S(node) = { N odd, all p | N are <= B, sigma(N) = 2N,
                                    v_r(N) = a_r for assigned r, p | N for included p, p does not divide N for excluded p }
  * I/X node:  children "p | N" and "p does not divide N" cover S(node)               (p must be an odd prime <= B)
  * R node on r:  r must divide every N in S(node) (r included, or r | sigma(prod r^a) and r odd);
                  every admissible exponent a of r (rows file) is either a child, or provably impossible:
                    J1  a < v_r(sigma_assigned)                      (then v_r(sigma N) > v_r(N))
                    J2  a odd and v_2(sigma_assigned) >= 1           (then v_2(sigma N) >= 2)
                    J3  some q | sigma(r^a) gets total valuation above its limit:
                        q = 2: > 1;  q excluded: > 0;  q assigned: > a_q;  q = r: > 0
                  (the reason printed by lpf.c is ignored; the C code's choice of r is not trusted, only that r is
                   required)
  * leaves:   LB   A * prod_{required q} (q+1)/q > 2
              UB   A * M / E < 2,   E = prod_{assigned u excluded} p/(p-1),  M = independent upper bound (mup_check.c)
              OVER A > 2
              EQ / SOL / NOFREE: reported (never expected for odd perfect numbers)
    with A = sigma(N_a)/N_a computed directly as prod (r^(a+1)-1)/(r-1) / prod r^a  (not from the rows file).
  * a node without any event must be an R node (on the largest required prime) all of whose exponents are
    rejected by J1/J2/J3.
Rows file: every factorization is re-multiplied against (p^(a+1)-1)/(p-1); primality of every factor is checked
with a deterministic Miller-Rabin (bases 2..37, valid below 3.3e24) written here.  Completeness of the rows is
NOT checked here (that is rowverify.c).

usage: tree_check.py B rowsfile logfile mupfile
"""
import sys, threading
from fractions import Fraction
from collections import Counter

B = int(sys.argv[1]); ROWS = sys.argv[2]; LOGF = sys.argv[3]; MUPF = sys.argv[4]

def is_prime(n):
    if n < 2: return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for p in small:
        if n % p == 0: return n == p
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in small:
        x = pow(a, d, n)
        if x == 1 or x == n - 1: continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True
assert B < 3 * 10**24

def oddP(q): return q % 2 == 1 and 3 <= q <= B and is_prime(q)

# ---- M: independent rigorous upper bound (product in directed-rounding integer floats, mup_check.c) ----
nm, ne, dm, de, cnt = map(int, open(MUPF).read().split())
sh = ne - de; M = Fraction(nm * 2**max(sh, 0), dm * 2**max(-sh, 0))
print(f"[tree] B={B}  M (independent) <= {float(M):.12f}  from {cnt} odd primes", flush=True)

# ---- rows ----
rows = {}; nfac = 0
for line in open(ROWS):
    if not line.endswith('\n'): break
    t = line.split(); p = int(t[0]); n = int(t[1]); adm = {}
    assert oddP(p), p
    for tok in t[2:2 + n]:
        a_s, rest = tok.split(':', 1); items = rest.split(','); a = int(a_s)
        f = Counter()
        for it in items[1:]:
            q, e = it.split('^'); q = int(q); e = int(e)
            assert e >= 1 and (q == 2 or oddP(q)), (p, a, q)
            f[q] += e
        assert len(items) - 1 == int(items[0])
        prod = 1
        for q, e in f.items(): prod *= q ** e
        assert prod * (p - 1) == p ** (a + 1) - 1, ("factorization wrong", p, a)
        assert a not in adm
        adm[a] = f; nfac += 1
    if p in rows: assert rows[p] == adm, ("conflicting duplicate row", p)
    rows[p] = adm
print(f"[tree] rows: {len(rows)} primes, {nfac} factorizations re-multiplied and primality-checked", flush=True)

# ---- log -> list of (depth, tokens) ----
lines = []
with open(LOGF) as f:
    head = f.readline(); assert head.startswith('# lpf B=%d k=2/1 mode=odd' % B), head
    for ln in f:
        if ln.startswith('#'):
            end = ln.strip(); break
        t = ln.split(); lines.append((int(t[0]), t[1:]))
    else:
        end = None
assert end is not None and end.startswith('# END'), "log has no END line (run not finished?)"
print(f"[tree] log: {len(lines)} event lines, {end}", flush=True)

stats = Counter(); errors = []
def err(msg):
    errors.append(msg)
    if len(errors) <= 20: print("[tree] ERROR", msg, flush=True)

def sigma_pp(r, a): return (r ** (a + 1) - 1) // (r - 1)

def derived(assigned, included):
    Sig = Counter()
    for r, a in assigned.items(): Sig.update(rows[r][a])
    req = {q for q, v in Sig.items() if v > 0 and q != 2} | set(included)
    req -= set(assigned)
    num = 1; den = 1
    for r, a in assigned.items(): num *= sigma_pp(r, a); den *= r ** a
    return Sig, req, Fraction(num, den)

def rejected(r, a, Sig, assigned, excluded):
    """J1/J2/J3 from scratch; returns reason or None"""
    if a < Sig.get(r, 0): return 'J1'
    if a % 2 == 1 and Sig.get(2, 0) >= 1: return 'J2'
    for q, e in rows[r][a].items():
        t = Sig.get(q, 0) + e
        if q == 2 and t > 1: return 'J3'
        if q == r: return 'J3self'
        if q in excluded and t > 0: return 'J3'
        if q in assigned and t > assigned[q]: return 'J3'
    return None

pos = 0
def node(depth, assigned, excluded, included):
    """consume the events of the node at `depth` starting at lines[pos]; check it"""
    global pos
    stats['nodes'] += 1
    ev = []   # (tokens, child_info)
    kids = []
    while pos < len(lines) and lines[pos][0] == depth:
        t = lines[pos][1]; pos += 1
        if t[0] in ('A', 'I', 'X', 'F'):
            kids.append(t)
            if t[0] == 'A':
                r, a = int(t[1]), int(t[2])
                na = dict(assigned); na[r] = a
                node(depth + 1, na, excluded, included)
            elif t[0] == 'I':
                p = int(t[1]); node(depth + 1, assigned, excluded, included | {p})
            elif t[0] == 'X':
                p = int(t[1]); node(depth + 1, assigned, excluded | {p}, included)
            else:
                err(f"F event at depth {depth} (not expected in odd mode)"); node(depth + 1, assigned, excluded, included)
        ev.append(t)
    if pos < len(lines) and lines[pos][0] > depth:
        err(f"malformed log at line {pos}: depth jump"); raise SystemExit(2)
    Sig, req, A = derived(assigned, included)
    # consistency of the state reached (informative)
    for q, v in Sig.items():
        if (q in excluded and v > 0) or (q in assigned and v > assigned[q]) or (q == 2 and v > 1):
            stats['inconsistent_states'] += 1; break
    kinds = {t[0] for t in ev}
    if len(ev) == 1 and ev[0][0] in ('LB', 'UB', 'OVER', 'EQ', 'SOL', 'NOFREE'):
        k = ev[0][0]; stats['leaf_' + k] += 1
        if k == 'LB':
            L = A
            for q in req: L *= Fraction(q + 1, q)
            if not L > 2: err(f"LB leaf not justified at depth {depth}")
        elif k == 'UB':
            E = Fraction(1)
            num = 1; den = 1
            for p in list(assigned) + list(excluded): num *= p; den *= p - 1
            if not A * M * den < 2 * num: err(f"UB leaf not justified at depth {depth} (A*M/E = {float(A*M*den/num)})")
        elif k == 'OVER':
            if not A > 2: err(f"OVER leaf not justified at depth {depth}")
        else:
            err(f"{k} leaf at depth {depth}: {ev[0]}  (would be an odd perfect number / unexpected)")
        return
    if kinds <= {'I', 'X'} and ev:
        stats['IX_nodes'] += 1
        if not (len(ev) == 2 and ev[0][0] == 'I' and ev[1][0] == 'X' and ev[0][1] == ev[1][1]):
            err(f"I/X node malformed at depth {depth}: {ev}"); return
        p = int(ev[0][1])
        if not oddP(p) or p in assigned or p in excluded: err(f"I/X on invalid prime {p} at depth {depth}")
        return
    if kinds <= {'R', 'A'}:
        stats['R_nodes'] += 1
        rs = {int(t[1]) for t in ev}
        if not ev:
            stats['R_nodes_silent'] += 1
            if not req: err(f"empty node with no required prime at depth {depth}"); return
            rs = {max(req)}
        if len(rs) != 1: err(f"R node with several primes {rs} at depth {depth}"); return
        r = rs.pop()
        if r not in req: err(f"branch on prime {r} that is not required at depth {depth}"); return
        if r not in rows: err(f"no row for {r}"); return
        children = {int(t[2]) for t in ev if t[0] == 'A'}
        for a in children:
            if a not in rows[r]: stats['child_not_in_row'] += 1
        for a in rows[r]:
            if a in children: continue
            why = rejected(r, a, Sig, assigned, excluded)
            if why is None: err(f"MISSING BRANCH: r={r} a={a} at depth {depth} not rejected and not explored")
            else: stats['rej_' + why] += 1
        return
    err(f"unclassifiable node at depth {depth}: {ev[:4]}")

def main():
    node(0, {}, frozenset(), frozenset())
    if pos != len(lines): err(f"trailing lines from {pos}")
    n_end = int(end.split('nodes=')[1].split()[0])
    print(f"[tree] stats: {dict(sorted(stats.items()))}", flush=True)
    if stats['nodes'] != n_end: print(f"[tree] note: tree has {stats['nodes']} nodes, C counted {n_end}", flush=True)
    print(f"[tree] {'OK' if not errors else 'FAIL'}: errors={len(errors)}", flush=True)

sys.setrecursionlimit(1_000_000)
threading.stack_size(1 << 29)
th = threading.Thread(target=main); th.start(); th.join()
sys.exit(1 if errors else 0)
