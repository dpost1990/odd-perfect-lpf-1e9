import sys; sys.path.insert(0,'.')
from closure_solver import Solver
from fractions import Fraction
B=int(sys.argv[1]); s=Solver(B,Fraction(2),True); s.logf=open(f'runs/py_{B}.log','w'); s.run(); s.logf.close(); print(B, s.nodes, s.solutions, flush=True)
