# O = Z[z]/(1+z+z^2+z^3+z^4), elements as tuples of 4 ints (basis 1,z,z^2,z^3)
def red(p):  # p list of coeffs any length
    p=list(p)+[0]*8
    for d in range(len(p)-1,4,-1):  # z^5=1
        p[d-5]+=p[d]; p[d]=0
    c4=p[4]; return tuple(p[i]-c4 for i in range(4))
def mul(a,b):
    r=[0]*8
    for i in range(4):
        for j in range(4): r[i+j]+=a[i]*b[j]
    return red(r)
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def sc(c,a): return tuple(c*x for x in a)
one=(1,0,0,0); z=(0,1,0,0)
def zp(k):
    r=one
    for _ in range(k%5): r=mul(r,z)
    return r
phi=red([1,1,0,0,1])
def lamdiv(t): return sum(t)%5==0
def div5lam(t):  # divisible by lambda^5 = 5*unit*lambda
    return all(x%5==0 for x in t) and lamdiv(tuple(x//5 for x in t))
def real(a,b): return add(sc(a,one),sc(b,phi))
res={}
for a1 in range(25):
  for b1 in range(5):
    X=real(a1,b1)
    if lamdiv(X): continue
    for a2 in range(25):
      for b2 in range(5):
        Y=real(a2,b2)
        if lamdiv(Y) or lamdiv(add(X,Y)): continue
        for k in range(5):
          L=mul(zp(-k),add(X,mul(z,Y))); R=mul(zp(k),add(X,mul(zp(4),Y)))
          if div5lam(add(L,sc(-1,R))): res[k]=res.get(k,0)+1
print(res)
