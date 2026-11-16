#!/usr/bin/env python3
"""
Prototype B (ideas agent): sigma(N) = k*N over B-smooth N as a pure 0/1 integer program.

Variables x[p,a] in {0,1}: "p^a || N", for every prime p <= B and every exponent a in the finite,
complete candidate set E(p) given by the Zsigmondy/ord lemma + cyclotomic smoothness (see
closure_solver.py).  Since every sigma(p^a) with x=1 factors over allowed primes, sigma(N) = k*N is
EQUIVALENT to the linear valuation balance
      for every prime q:  sum_{p,a} v_q(sigma(p^a)) x[p,a]  =  sum_a a*x[q,a]  +  v_q(k)
plus  sum_a x[p,a] <= 1  and  sum x >= 1.   (No abundancy / floating point needed at all.)
Solved with OR-tools CP-SAT (exact integer arithmetic), 1 worker, enumerating all solutions.
"""
import sys, time, argparse
from fractions import Fraction
from ortools.sat.python import cp_model
from closure_solver import Solver

def build_and_solve(B, k, odd, time_limit=600, verbose=False):
    t0 = time.time()
    S = Solver(B, Fraction(k), odd)
    S.allowed_sigma_primes_sorted = sorted(S.allowed_sigma_primes)
    var = {}  # (p,a) -> (boolvar, factor dict)
    for p in S.P:
        for a in S.exp_candidates(p, frozenset()):
            f = S.sigma_fact(p, a)
            if f is None or p in f: continue
            # parity shortcut not needed: valuation of 2 handled by constraints
            var[(p, a)] = f
    t_build = time.time() - t0
    m = cp_model.CpModel()
    x = {pa: m.NewBoolVar(f"x_{pa[0]}_{pa[1]}") for pa in var}
    byp = {}
    for (p, a) in var: byp.setdefault(p, []).append(a)
    for p, al in byp.items():
        m.Add(sum(x[(p, a)] for a in al) <= 1)
    rows = {}
    for (p, a), f in var.items():
        for q, e in f.items(): rows.setdefault(q, []).append((e, (p, a)))
    qs = set(rows) | set(S.kval) | set(byp)
    for q in qs:
        lhs = sum(e * x[pa] for e, pa in rows.get(q, []))
        rhs = sum(a * x[(q, a)] for a in byp.get(q, [])) + S.kval.get(q, 0)
        m.Add(lhs == rhs)
    m.Add(sum(x.values()) >= 1)
    solver = cp_model.CpSolver()
    solver.parameters.num_workers = 1
    solver.parameters.enumerate_all_solutions = True
    solver.parameters.max_time_in_seconds = time_limit
    sols = []
    class CB(cp_model.CpSolverSolutionCallback):
        def __init__(s): super().__init__()
        def on_solution_callback(s):
            N = 1
            for pa, v in x.items():
                if s.Value(v): N *= pa[0] ** pa[1]
            sols.append(N)
    st = solver.Solve(m, CB())
    return dict(B=B, k=str(k), odd=odd, vars=len(var), primes_with_vars=len(byp), cons=len(qs),
                status=solver.StatusName(st), build_s=round(t_build, 2),
                solve_s=round(solver.WallTime(), 2), solutions=sorted(sols))

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--B', type=int, default=1000)
    ap.add_argument('--k', default='2')
    ap.add_argument('--odd', action='store_true')
    ap.add_argument('--time-limit', type=float, default=600)
    a = ap.parse_args()
    print(build_and_solve(a.B, Fraction(a.k), a.odd, a.time_limit))
