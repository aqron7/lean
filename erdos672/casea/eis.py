exec(open('ex1.py').read().split('res={}')[0])
import itertools
from sympy import isprime
def norm(a):
    # product of conjugates via numeric
    import cmath
    r=1
    for c in range(1,5):
        w=cmath.exp(2j*cmath.pi*c/5); r*=sum(a[i]*w**i for i in range(4))
    return round(r.real)
def mod2class(a):  # a^3 mod 2 expressed: compute a^3, reduce mod 2, compare with z^i mod 2
    a3=mul(mul(a,a),a); r=tuple(x%2 for x in a3)
    for i in range(5):
        if tuple(x%2 for x in zp(i))==r: return i
    return None
def primary(a): # ≡ rational mod lambda^2
    for c in range(25):
        t=add(a,sc(-c,one))
        # lambda^2 | t: t/(1-z) then lamdiv
        if lamdiv(t):
            p=mul(t,(4,3,2,1))
            if all(x%5==0 for x in p) and lamdiv(tuple(x//5 for x in p)): return True
    return False
gens={}
R=range(-4,5)
for a in itertools.product(R,repeat=4):
    n=abs(norm(a))
    if n>1 and n<400 and isprime(n) and n%5==1: gens.setdefault(n,[]).append(a)
bad=0;tot=0
for p in sorted(gens):
    k=(p-1)//5
    for a in gens[p]:
        if not primary(a): continue
        # find d with a ≡0 mod (p, z-d)
        for d in range(2,p):
            if pow(d,5,p)!=1: continue
            if sum(a[i]*pow(d,i,p) for i in range(4))%p==0: break
        e=pow(2,k,p); i=[j for j in range(5) if pow(d,j,p)==e][0]   # (2/P)=z^i
        u=mod2class(a)
        tot+=1
        if u!=i: bad+=1
    print(p, 'i=',i,'u=',u)
print(tot,bad)
