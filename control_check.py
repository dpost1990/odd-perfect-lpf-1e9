"""Independent check of closure_solver positive controls against OEIS lists (sympy path)."""
import sys, sympy
from closure_solver import Solver
def smooth_list(fn, B):
    out=[]
    for line in open(fn):
        if line.startswith('#') or not line.strip(): continue
        n=int(line.split()[1]); f=sympy.factorint(n)
        if max(f)<=B: out.append(n)
    return sorted(out)
B=int(sys.argv[1]); k=int(sys.argv[2]); fn=sys.argv[3]
exp=smooth_list(fn,B)
s=Solver(B,k,False).run()
got=sorted(s.solutions)
for n in got: assert sympy.divisor_sigma(n)==k*n
print(f"B={B} k={k}: solver {len(got)} sols, OEIS {B}-smooth {len(exp)}; equal={got==exp}; nodes={s.nodes}")
if got!=exp: print("missing",set(exp)-set(got),"extra",set(got)-set(exp))
