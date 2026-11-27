exec(open('ex1.py').read().split('res={}')[0])
from collections import Counter
def sigma(a): # z->z^4
    r=[0]*20
    for i in range(4): r[(4*i)%5]+=a[i]
    return red(r)
phip=[one]
for _ in range(4): phip.append(mul(phip[-1],phi))
def israt(t): # t ≡ integer mod lambda^5 ?
    for c in range(25):
        if div5lam(add(t,sc(-c,one))): return True
    return False
def nclass(t): # n with t/phi^n ≡ rational, t real-ish
    out=[]
    for n in range(5):
        # t ≡ phi^n * c  <=> exists c
        for c in range(25):
            if div5lam(add(t,sc(-c,phip[n]))): out.append(n); break
    return tuple(out)
C=Counter()
import itertools
for co in itertools.product(range(5),repeat=4):
  for ex in range(5):  # lift a bit: rho mod 5 then add 5*ex*... skip; rho mod 5 enough? use rho + 0
    rho=tuple(co); 
    if lamdiv(rho): continue
    s=sigma(rho)
    B=[add(rho,mul(zp(i),s)) for i in range(5)]
    if any(lamdiv(b) for b in B): continue
    t1=mul(zp(2),B[1]); t4=mul(zp(3),B[4]); t2=mul(zp(4),B[2]); t3=mul(zp(1),B[3])
    C[(nclass(B[0]),nclass(t1),nclass(t4),nclass(t2),nclass(t3))]+=1
    break
for k,v in sorted(C.items()): print(k,v)
