import itertools, cmath
from fractions import Fraction as Fr
exec(open('ex3.py').read().split('C=Counter()')[0])
def inv(a): # inverse in Q(z) via conjugates numeric -> use exact: a^-1 = prod of other conj / norm
    import numpy
    pass
def tau(a,c):
    r=[0]*20
    for i in range(4): r[(c*i)%5]+=a[i]
    return red(r)
def N(a):
    r=1
    for c in range(1,5):
        w=cmath.exp(2j*cmath.pi*c/5); r*=sum(a[i]*w**i for i in range(4))
    return round(r.real)
def phipow(n):
    r=one; b=phi if n>=0 else red([0,0,1,1]) ; b = phi if n>=0 else add(phi,sc(-1,one))  # phi^-1 = phi-1
    for _ in range(abs(n)): r=mul(r,b)
    return r
# (zeta^4 - zeta) sigma rho = b4 - b1 ; divide by zeta^4-zeta: multiply by inverse = conj stuff / norm
d=add(zp(4),sc(-1,z)); Nd=N(d)
dc=mul(mul(tau(d,2),tau(d,3)),tau(d,4))  # d * dc = Nd
sols=[]
for a in range(-12,13):
  for b in range(-12,13):
    for s1 in (1,-1):
      for s4 in (1,-1):
        b1=mul(zp(-2),sc(s1,phipow(a))); b4=mul(zp(-3),sc(s4,phipow(b)))
        num=mul(add(b4,sc(-1,b1)),dc)
        if any(x%Nd for x in num): continue
        sr=tuple(x//Nd for x in num)
        rho=add(b1,sc(-1,mul(z,sr)))
        if sigma(rho)!=sr: continue
        B0=add(rho,sr)
        if abs(N(B0))!=16: continue
        if all(x%2==0 for x in B0) and abs(N(tuple(x//2 for x in B0)))==1:
            sols.append((a,b,s1,s4,N(rho),rho))
print(len(sols)); print(set(s[4] for s in sols)); print(sols[:6])
