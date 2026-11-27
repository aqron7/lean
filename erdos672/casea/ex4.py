exec(open('ex3.py').read().split('C=Counter()')[0])
from collections import Counter
import itertools
def lam4(t): # divisible by lambda^4 ~ 5
    return all(x%5==0 for x in t)
C=Counter()
for co in itertools.product(range(5),repeat=4):
    rho=tuple(co)
    if lamdiv(rho): continue
    s=sigma(rho)
    if not lam4(add(rho,sc(-1,s))): continue
    B=[add(rho,mul(zp(i),s)) for i in range(5)]
    t1=mul(zp(2),B[1]); t4=mul(zp(3),B[4])
    a=nclass(t1); b=nclass(t4)
    C[(nclass(B[0]),a,b)]+=1
print(C)
