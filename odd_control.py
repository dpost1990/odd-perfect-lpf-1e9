"""Odd positive control: brute-force all odd B-smooth N <= X, group by sigma(N)/N, and check the
closure solver finds (at least) exactly those <= X for several rational targets; extra (> X)
solutions are re-verified with sympy.divisor_sigma (independent code path)."""
import sys, sympy, random
from fractions import Fraction
from closure_solver import Solver, primes_upto
B=int(sys.argv[1]); X=int(sys.argv[2]); ntargets=int(sys.argv[3])
Ps=[p for p in primes_upto(B) if p>2]
# enumerate odd B-smooth numbers <= X with their abundancy
groups={}
def rec(i,n,sig):
    groups.setdefault(Fraction(sig,n),[]).append(n)
    for j in range(i,len(Ps)):
        p=Ps[j]
        if n*p> X: break
        m=n*p; e=1
        while m<=X:
            rec(j+1,m,sig*(p**(e+1)-1)//(p-1)); m*=p; e+=1
rec(0,1,1)
random.seed(1)
cands=sorted([r for r,v in groups.items() if r!=1 and len(v)>=2], key=lambda r:(-len(groups[r]), r.denominator))[:40]
targets=random.sample(cands,min(ntargets,len(cands)))
targets+= [r for r,v in groups.items() if r.numerator%2==0 and r!=1][:3]
okall=True
for r in targets:
    s=Solver(B,r,True,time_limit=120).run()
    got=sorted(s.solutions); small=[n for n in got if n<=X]; exp=sorted(groups[r])
    for n in got: assert sympy.divisor_sigma(n)*r.denominator==r.numerator*n and max(sympy.factorint(n))<=B and n%2
    ok= small==exp and not s.aborted
    okall&=ok
    print(f"target {r}: brute(<= {X}) {len(exp)}  solver total {len(got)} (<=X: {len(small)}) nodes={s.nodes} ok={ok}")
print("ALL OK" if okall else "MISMATCH")
