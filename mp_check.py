import sys, subprocess, sympy
B,k,fn,lim=int(sys.argv[1]),int(sys.argv[2]),sys.argv[3],sys.argv[4]
out=subprocess.run(['./lpf',str(B),str(k),'even','4',f'runs/mp_rows_{B}_{k}.txt','-',lim],capture_output=True,text=True)
res=[l for l in out.stdout.splitlines() if l.startswith('RESULT')]
if not res: print('ABORT', out.stderr[-300:]); sys.exit()
got=sorted(int(l.split()[1]) for l in out.stdout.splitlines() if l.startswith('SOL'))
for n in got: assert sympy.divisor_sigma(n)==k*n
exp=[]
for l in open(fn):
    if l.strip() and not l.startswith('#'):
        n=int(l.split()[1]); f=sympy.factorint(n)
        if max(f)<=B: exp.append(n)
exp.sort()
print(res[0]); print(f"k={k} B={B}: solver {len(got)}, OEIS B-smooth {len(exp)}, OEIS subset of solver: {set(exp)<=set(got)}, extra: {sorted(set(got)-set(exp))[:5]}")
