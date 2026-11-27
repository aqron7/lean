exec(open('ex3.py').read().split('C=Counter()')[0])
from collections import Counter
import itertools
lamv=red([1,-1])
def lampow(n):
    r=one
    for _ in range(n): r=mul(r,lamv)
    return r
# divisibility by lambda^e: test via t = lam^e * q ; use valuation via norms: compute by repeated division check
def val(t,maxe=6):
    # lambda | t iff sum coeffs ≡0 mod5; divide t by lambda exactly: solve t = (1-z) q
    e=0
    while e<maxe and lamdiv(t):
        # q = t/(1-z): coefficients: t=q-zq ; solve in basis using q = t * (1-z)^{-1}; (1-z)^{-1} = (1/5)*u ... use brute: t*(?)/5
        # (1-z)*(4+3z+2z^2+z^3) = 5 -> 1/(1-z) = (4+3z+2z^2+z^3)/5
        p=mul(t,(4,3,2,1))
        if any(x%5 for x in p): break
        t=tuple(x//5 for x in p); e+=1
    return e
C=Counter()
for co in itertools.product(range(5),repeat=4):
    rho=tuple(co)
    if lamdiv(rho): continue
    s=sigma(rho)
    v=val(add(rho,sc(-1,s)))
    B=[add(rho,mul(zp(i),s)) for i in range(5)]
    if any(lamdiv(b) for b in B): continue
    a=nclass(mul(zp(2),B[1])); b=nclass(mul(zp(3),B[4]))
    C[(min(v,4),(b[0]-a[0])%5)]+=1
for k in sorted(C): print(k,C[k])
