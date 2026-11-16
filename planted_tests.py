"""Planted-solution / positive-control tests for the C solver ./lpf.
 (1) odd rational targets: brute-force all odd B-smooth N <= X, pick targets r=sigma(N)/N; the solver must
     return every brute-force solution <= X (and possibly more > X); every returned N re-verified by sympy.
 (2) multiperfect (even allowed): compare with the B-smooth members of OEIS b-files (A000396, A005820,
     A027687, A046060, A046061)."""
import sys, subprocess, random, sympy
from fractions import Fraction
def run(B, k, mode, rows):
    print('target',k,flush=True); out = subprocess.run(['./lpf', str(B), f'{k.numerator}/{k.denominator}', mode, '2', rows, '-'], capture_output=True, text=True)
    if 'RESULT' not in out.stdout: print('FAIL', out.stdout[-500:], out.stderr[-1500:]); sys.exit(1)
    out=out.stdout
    res = [l for l in out.splitlines() if l.startswith('RESULT')][0]
    sols = sorted(int(l.split()[1]) for l in out.splitlines() if l.startswith('SOL'))
    return res, sols
def primes_upto(n): return list(sympy.primerange(2, n+1))
ok_all = True
B=int(sys.argv[1]); X=int(sys.argv[2]); ntar=int(sys.argv[3])
Ps=[p for p in primes_upto(B) if p>2]; groups={}
def rec(i,n,sig):
    groups.setdefault(Fraction(sig,n),[]).append(n)
    for j in range(i,len(Ps)):
        p=Ps[j]
        if n*p>X: break
        m=n*p; e=1
        while m<=X:
            rec(j+1,m,sig*(p**(e+1)-1)//(p-1)); m*=p; e+=1
rec(0,1,1)
random.seed(7)
cands=[r for r,v in groups.items() if r!=1 and max(sympy.factorint(r.numerator*r.denominator))<=B]
big=sorted(cands,key=lambda r:(-len(groups[r]),r.denominator))[:ntar]
targets=big+random.sample(cands,ntar)
for r in targets:
    res,got=run(B,r,'odd',f'runs/pl_rows_{B}_{r.numerator}_{r.denominator}.txt')
    small=[n for n in got if n<=X]; exp=sorted(groups[r])
    for n in got: assert sympy.divisor_sigma(n)*r.denominator==r.numerator*n and n%2 and max(sympy.factorint(n))<=B, n
    ok = small==exp; ok_all&=ok
    print(f"odd target {r}: brute {len(exp)} solver<=X {len(small)} total {len(got)} ok={ok}")
print("PLANTED", "ALL OK" if ok_all else "MISMATCH")
